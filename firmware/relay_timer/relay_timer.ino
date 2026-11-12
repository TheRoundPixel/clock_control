/*
  ТАЙМЕР РЕЛЕ ПО РАСПИСАНИЮ СО СМАРТФОНА
  Arduino Nano + DS1302 (часы) + HC-06 (Bluetooth) + твердотельное реле G3MB-202P

  ---------------- ПОДКЛЮЧЕНИЕ ----------------
  DS1302:  VCC -> 5V   GND -> GND   CLK -> D5   DAT -> D6   RST -> D7
  HC-06:   VCC -> 5V   GND -> GND
           TXD -> D10
           RXD <- D11 через делитель: D11 --[1 кОм]--+--[2 кОм]-- GND
                                                    |
                                                  RXD HC-06
  Реле:    DC+ -> 5V   DC- -> GND   CH1 -> D4
           Силовые клеммы реле — в разрыв ФАЗЫ 220 В, идущей на блок питания ленты.
           (Реле только для переменного тока! Цепь 12/24 В постоянного тока им коммутировать нельзя.)

  ---------------- КОМАНДЫ (каждая строка заканчивается переводом строки) ----------------
  HELP                          — список команд
  STATUS                        — время, состояние реле, число правил
  TIME 2026-11-12 10:58:00      — установить дату и время (можно и 12.11.2026 10:58)
  TIME 10:58:30                 — поправить только время
  ADD 08:00 23:00               — включать с 08:00 до 23:00 каждый день
  ADD 18:30 01:00 12345         — с 18:30 до 01:00, только Пн–Пт (1=Пн ... 7=Вс)
  LIST                          — показать правила
  EDIT 2 19:00 01:00 12345      — изменить правило №2
  EN 2 0                        — временно отключить правило №2 (EN 2 1 — включить)
  DEL 2                         — удалить правило №2
  CLEAR                         — удалить все правила
  ON / OFF                      — включить/выключить вручную до следующего переключения по расписанию
  AUTO                          — отменить ручной режим

  Приложение для Android шлёт те же команды с префиксом «!» (например, !ADD 08:00 23:00 1234567)
  и получает в ответ полное состояние в машинном виде:
    #S <время_установлено 0/1> <ГГГГ-ММ-ДД> <ЧЧ:ММ:СС> <реле 0/1> <ручной режим -1/0/1>
    #R <№> <ЧЧ:ММ вкл> <ЧЧ:ММ выкл> <маска дней> <правило включено 0/1>
    #E   — конец ответа
  GET — выдать это состояние вручную.

  Правила хранятся в EEPROM, время — в DS1302 (идёт от батарейки).
  После пропадания питания реле сразу возвращается в положение, положенное по расписанию.
*/

#include <SoftwareSerial.h>
#include <EEPROM.h>

// ---------- Пины ----------
const uint8_t PIN_BT_RX   = 10;  // <- TXD HC-06
const uint8_t PIN_BT_TX   = 11;  // -> RXD HC-06 (через делитель)
const uint8_t PIN_RTC_CLK = 5;
const uint8_t PIN_RTC_DAT = 6;
const uint8_t PIN_RTC_RST = 7;
const uint8_t PIN_RELAY   = 4;
const uint8_t PIN_LED     = 13;  // встроенный светодиод повторяет состояние реле

const bool    RELAY_ACTIVE_HIGH = true;  // реле «высокого уровня»
const long    BT_BAUD    = 9600;         // скорость HC-06 по умолчанию
const uint8_t MAX_RULES  = 8;

SoftwareSerial bt(PIN_BT_RX, PIN_BT_TX);

// ---------- Данные ----------
struct DateTime {
  uint16_t year;
  uint8_t month, day, hour, minute, second;
};

struct Rule {
  uint8_t onH, onM, offH, offM;
  uint8_t days;  // бит0 = Пн ... бит6 = Вс
  uint8_t en;    // 1 — правило действует, 0 — временно отключено
};

struct Config {
  uint8_t magic;
  uint8_t count;
  Rule rules[MAX_RULES];
};

const uint8_t CFG_MAGIC = 0x5B;
const uint8_t RTC_RAM_MAGIC = 0xA5;  // метка «время установлено» в ОЗУ DS1302
Config cfg;

DateTime now;
bool timeSet = false;      // время в часах установлено и часы идут
bool haveTime = false;     // последнее чтение часов удачное
int8_t overrideState = -1; // -1 — нет ручного режима, 0 — выкл, 1 — вкл
bool autoState = false;
bool relayState = false;
bool firstEval = true;
bool btMachine = false;    // по Bluetooth работает приложение — не слать ему лишний текст

// «Пустой» поток: в него уходят текстовые ответы на команды приложения
class NullStream : public Stream {
 public:
  size_t write(uint8_t) override { return 1; }
  int available() override { return 0; }
  int read() override { return -1; }
  int peek() override { return -1; }
};
NullStream nullOut;

const char* const DAY_NAMES[7] = {"Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"};

// ================= DS1302 =================
uint8_t bcd2dec(uint8_t v) { return (v >> 4) * 10 + (v & 0x0F); }
uint8_t dec2bcd(uint8_t v) { return ((v / 10) << 4) | (v % 10); }

void rtcWriteByte(uint8_t v, bool thenRead) {
  pinMode(PIN_RTC_DAT, OUTPUT);
  for (uint8_t i = 0; i < 8; i++) {
    digitalWrite(PIN_RTC_DAT, v & 1);
    delayMicroseconds(1);
    digitalWrite(PIN_RTC_CLK, HIGH);
    delayMicroseconds(1);
    if (i == 7 && thenRead) pinMode(PIN_RTC_DAT, INPUT);
    digitalWrite(PIN_RTC_CLK, LOW);
    delayMicroseconds(1);
    v >>= 1;
  }
}

uint8_t rtcReadByte() {
  uint8_t v = 0;
  for (uint8_t i = 0; i < 8; i++) {
    if (digitalRead(PIN_RTC_DAT)) v |= (1 << i);
    digitalWrite(PIN_RTC_CLK, HIGH);
    delayMicroseconds(1);
    digitalWrite(PIN_RTC_CLK, LOW);
    delayMicroseconds(1);
  }
  return v;
}

void rtcStart(uint8_t cmd) {
  digitalWrite(PIN_RTC_RST, LOW);
  digitalWrite(PIN_RTC_CLK, LOW);
  digitalWrite(PIN_RTC_RST, HIGH);
  delayMicroseconds(4);
  rtcWriteByte(cmd, cmd & 0x01);
}

void rtcStop() {
  digitalWrite(PIN_RTC_RST, LOW);
  delayMicroseconds(4);
}

uint8_t rtcReadReg(uint8_t addr) {
  rtcStart(addr | 0x01);
  uint8_t v = rtcReadByte();
  rtcStop();
  return v;
}

void rtcWriteReg(uint8_t addr, uint8_t v) {
  rtcStart(addr & 0xFE);
  rtcWriteByte(v, false);
  rtcStop();
}

uint8_t daysInMonth(uint16_t y, uint8_t m) {
  static const uint8_t d[12] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
  if (m == 2 && ((y % 4 == 0 && y % 100 != 0) || y % 400 == 0)) return 29;
  return d[m - 1];
}

// 1 = Пн ... 7 = Вс
uint8_t dayOfWeek(uint16_t y, uint8_t m, uint8_t d) {
  static const uint8_t t[12] = {0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4};
  if (m < 3) y--;
  uint8_t s = (y + y / 4 - y / 100 + y / 400 + t[m - 1] + d) % 7;  // 0 = Вс
  return s == 0 ? 7 : s;
}

bool validDateTime(const DateTime& t) {
  return t.year >= 2000 && t.year <= 2099 && t.month >= 1 && t.month <= 12 &&
         t.day >= 1 && t.day <= daysInMonth(t.year, t.month) &&
         t.hour < 24 && t.minute < 60 && t.second < 60;
}

void rtcInit() {
  digitalWrite(PIN_RTC_RST, LOW);
  digitalWrite(PIN_RTC_CLK, LOW);
  pinMode(PIN_RTC_RST, OUTPUT);
  pinMode(PIN_RTC_CLK, OUTPUT);
  pinMode(PIN_RTC_DAT, INPUT);

  rtcWriteReg(0x8E, 0x00);  // снять защиту записи
  rtcWriteReg(0x90, 0x00);  // подзарядка выключена (батарейку CR2032 заряжать нельзя)
  uint8_t sec = rtcReadReg(0x80);
  if (sec & 0x80) {         // часы стояли (новая/севшая батарейка) — запустить
    rtcWriteReg(0x80, 0x00);
    rtcWriteReg(0xC0, 0x00);  // время не установлено
  }
  timeSet = (rtcReadReg(0xC0) == RTC_RAM_MAGIC);
  rtcWriteReg(0x8E, 0x80);  // защита записи
}

bool rtcRead(DateTime& t) {
  uint8_t r[7];
  rtcStart(0xBF);  // пакетное чтение
  for (uint8_t i = 0; i < 7; i++) r[i] = rtcReadByte();
  rtcStop();
  if (r[0] & 0x80) return false;  // часы остановлены
  t.second = bcd2dec(r[0] & 0x7F);
  t.minute = bcd2dec(r[1] & 0x7F);
  if (r[2] & 0x80) {  // 12-часовой режим
    uint8_t h = bcd2dec(r[2] & 0x1F) % 12;
    if (r[2] & 0x20) h += 12;
    t.hour = h;
  } else {
    t.hour = bcd2dec(r[2] & 0x3F);
  }
  t.day = bcd2dec(r[3] & 0x3F);
  t.month = bcd2dec(r[4] & 0x1F);
  t.year = 2000 + bcd2dec(r[6]);
  return validDateTime(t);
}

void rtcWrite(const DateTime& t) {
  rtcWriteReg(0x8E, 0x00);
  rtcWriteReg(0x80, 0x80);  // остановить на время записи
  rtcWriteReg(0x82, dec2bcd(t.minute));
  rtcWriteReg(0x84, dec2bcd(t.hour));  // 24-часовой режим
  rtcWriteReg(0x86, dec2bcd(t.day));
  rtcWriteReg(0x88, dec2bcd(t.month));
  rtcWriteReg(0x8A, dayOfWeek(t.year, t.month, t.day));
  rtcWriteReg(0x8C, dec2bcd(t.year - 2000));
  rtcWriteReg(0x80, dec2bcd(t.second));  // CH = 0 — пуск
  rtcWriteReg(0xC0, RTC_RAM_MAGIC);
  rtcWriteReg(0x8E, 0x80);
}

// ================= Настройки =================
void loadConfig() {
  EEPROM.get(0, cfg);
  if (cfg.magic != CFG_MAGIC || cfg.count > MAX_RULES) {
    cfg.magic = CFG_MAGIC;
    cfg.count = 0;
    EEPROM.put(0, cfg);
  }
}

void saveConfig() { EEPROM.put(0, cfg); }

// ================= Расписание =================
bool dayIn(uint8_t mask, uint8_t dow) { return mask & (1 << (dow - 1)); }

bool ruleActive(const Rule& r, uint16_t minNow, uint8_t dow) {
  if (!r.en) return false;
  uint16_t on = r.onH * 60 + r.onM;
  uint16_t off = r.offH * 60 + r.offM;
  uint8_t yesterday = (dow == 1) ? 7 : dow - 1;
  if (on < off) return dayIn(r.days, dow) && minNow >= on && minNow < off;
  // интервал через полночь: день правила — день включения
  return (minNow >= on && dayIn(r.days, dow)) || (minNow < off && dayIn(r.days, yesterday));
}

bool scheduleState(const DateTime& t) {
  uint16_t m = t.hour * 60 + t.minute;
  uint8_t dow = dayOfWeek(t.year, t.month, t.day);
  for (uint8_t i = 0; i < cfg.count; i++)
    if (ruleActive(cfg.rules[i], m, dow)) return true;
  return false;
}

// ================= Вывод =================
void print2(Stream& s, uint8_t v) {
  if (v < 10) s.print('0');
  s.print(v);
}

void printHM(Stream& s, uint8_t h, uint8_t m) {
  print2(s, h);
  s.print(':');
  print2(s, m);
}

void printDateTime(Stream& s, const DateTime& t) {
  s.print(t.year);
  s.print('-');
  print2(s, t.month);
  s.print('-');
  print2(s, t.day);
  s.print(' ');
  printHM(s, t.hour, t.minute);
  s.print(':');
  print2(s, t.second);
  s.print(' ');
  s.print(DAY_NAMES[dayOfWeek(t.year, t.month, t.day) - 1]);
}

void printDays(Stream& s, uint8_t mask) {
  if (mask == 0x7F) {
    s.print(F("каждый день"));
    return;
  }
  bool first = true;
  for (uint8_t d = 0; d < 7; d++) {
    if (mask & (1 << d)) {
      if (!first) s.print(' ');
      s.print(DAY_NAMES[d]);
      first = false;
    }
  }
}

void printRules(Stream& s) {
  if (cfg.count == 0) {
    s.println(F("Правил нет. Добавьте: ADD 08:00 23:00"));
    return;
  }
  for (uint8_t i = 0; i < cfg.count; i++) {
    const Rule& r = cfg.rules[i];
    s.print(i + 1);
    s.print(F(") "));
    printHM(s, r.onH, r.onM);
    s.print(F(" - "));
    printHM(s, r.offH, r.offM);
    s.print(F(", "));
    printDays(s, r.days);
    if (!r.en) s.print(F(" (отключено)"));
    s.println();
  }
}

void printMachine(Stream& s) {
  s.print(F("#S "));
  s.print(timeSet ? 1 : 0);
  s.print(' ');
  if (haveTime) {
    s.print(now.year);
    s.print('-');
    print2(s, now.month);
    s.print('-');
    print2(s, now.day);
    s.print(' ');
    printHM(s, now.hour, now.minute);
    s.print(':');
    print2(s, now.second);
  } else {
    s.print(F("0000-00-00 00:00:00"));
  }
  s.print(' ');
  s.print(relayState ? 1 : 0);
  s.print(' ');
  s.println(overrideState);
  for (uint8_t i = 0; i < cfg.count; i++) {
    const Rule& r = cfg.rules[i];
    s.print(F("#R "));
    s.print(i + 1);
    s.print(' ');
    printHM(s, r.onH, r.onM);
    s.print(' ');
    printHM(s, r.offH, r.offM);
    s.print(' ');
    s.print(r.days);
    s.print(' ');
    s.println(r.en ? 1 : 0);
  }
  s.println(F("#E"));
}

void printStatus(Stream& s) {
  s.print(F("Время: "));
  if (!timeSet) s.println(F("НЕ УСТАНОВЛЕНО (TIME ГГГГ-ММ-ДД ЧЧ:ММ)"));
  else if (!haveTime) s.println(F("ошибка чтения часов, проверьте DS1302"));
  else { printDateTime(s, now); s.println(); }
  s.print(F("Реле: "));
  s.print(relayState ? F("ВКЛ") : F("ВЫКЛ"));
  s.println(overrideState >= 0 ? F(" (вручную до след. переключения)") : F(" (по расписанию)"));
  s.print(F("Правил: "));
  s.print(cfg.count);
  s.print('/');
  s.println(MAX_RULES);
}

void printHelp(Stream& s) {
  s.println(F("Команды:"));
  s.println(F("STATUS"));
  s.println(F("TIME 2026-11-12 10:58:00 | TIME 10:58"));
  s.println(F("ADD 08:00 23:00 [12345] (1=Пн..7=Вс)"));
  s.println(F("EDIT n 08:00 23:00 [12345]"));
  s.println(F("EN n 0|1 (отключить/включить правило)"));
  s.println(F("LIST | DEL n | CLEAR"));
  s.println(F("ON | OFF | AUTO"));
}

// ================= Управление реле =================
void setRelay(bool on) {
  relayState = on;
  digitalWrite(PIN_RELAY, (on == RELAY_ACTIVE_HIGH) ? HIGH : LOW);
  digitalWrite(PIN_LED, on ? HIGH : LOW);
}

void reportChange(const __FlashStringHelper* why) {
  Stream* outs[2] = {&Serial, &bt};
  for (uint8_t i = 0; i < 2; i++) {
    if (i == 1 && btMachine) continue;
    Stream& s = *outs[i];
    if (haveTime) {
      printHM(s, now.hour, now.minute);
      s.print(' ');
    }
    s.print(F("Реле "));
    s.print(relayState ? F("ВКЛ") : F("ВЫКЛ"));
    s.print(F(" ("));
    s.print(why);
    s.println(')');
  }
}

void evaluate() {
  haveTime = timeSet && rtcRead(now);
  if (haveTime) {
    bool a = scheduleState(now);
    if (a != autoState && !firstEval) overrideState = -1;  // расписание переключилось — ручной режим снят
    autoState = a;
  }
  // если часы не прочитались — расписание остаётся в прежнем положении
  firstEval = false;
  bool target = (overrideState >= 0) ? (overrideState == 1) : autoState;
  if (target != relayState) {
    setRelay(target);
    reportChange(overrideState >= 0 ? F("вручную") : F("по расписанию"));
  }
}

// ================= Команды =================
void toUpper(char* s) {
  for (; *s; s++)
    if (*s >= 'a' && *s <= 'z') *s -= 32;
}

bool parseDays(const char* s, uint8_t& mask) {
  mask = 0;
  for (; *s; s++) {
    if (*s < '1' || *s > '7') return false;
    mask |= 1 << (*s - '1');
  }
  return mask != 0;
}

void cmdTime(Stream& out, const char* arg) {
  int Y = 0, Mo = 0, D = 0, h = 0, m = 0, s = 0;
  DateTime t;
  int n = sscanf(arg, "%d-%d-%d %d:%d:%d", &Y, &Mo, &D, &h, &m, &s);
  if (n < 5) {
    s = 0;
    n = sscanf(arg, "%d.%d.%d %d:%d:%d", &D, &Mo, &Y, &h, &m, &s);
  }
  if (n >= 5) {
    t.year = Y; t.month = Mo; t.day = D;
  } else {
    s = 0;
    n = sscanf(arg, "%d:%d:%d", &h, &m, &s);
    if (n < 2) { out.println(F("Формат: TIME 2026-11-12 10:58:00 или TIME 10:58")); return; }
    if (!timeSet || !rtcRead(t)) { out.println(F("Сначала задайте дату: TIME ГГГГ-ММ-ДД ЧЧ:ММ")); return; }
  }
  if (h < 0 || m < 0 || s < 0 || Y < 0 || Mo < 0 || D < 0) { out.println(F("Неверное значение")); return; }
  t.hour = h; t.minute = m; t.second = s;
  if (!validDateTime(t)) { out.println(F("Неверные дата или время")); return; }
  rtcWrite(t);
  timeSet = true;
  firstEval = true;  // пересчитать расписание без сброса ручного режима
  evaluate();
  out.print(F("Время установлено: "));
  printDateTime(out, t);
  out.println();
}

bool parseRule(Stream& out, const char* arg, Rule& r) {
  int h1, m1, h2, m2;
  char days[9] = "";
  int n = sscanf(arg, "%d:%d %d:%d %8s", &h1, &m1, &h2, &m2, days);
  if (n < 4) { out.println(F("Формат: 08:00 23:00 [12345]")); return false; }
  if (h1 < 0 || h1 > 23 || h2 < 0 || h2 > 23 || m1 < 0 || m1 > 59 || m2 < 0 || m2 > 59) {
    out.println(F("Неверное время")); return false;
  }
  if (h1 == h2 && m1 == m2) { out.println(F("Время включения и выключения совпадают")); return false; }
  uint8_t mask = 0x7F;
  if (n == 5 && !parseDays(days, mask)) { out.println(F("Дни — цифры 1..7, например 12345")); return false; }
  r.onH = h1; r.onM = m1; r.offH = h2; r.offM = m2; r.days = mask; r.en = 1;
  return true;
}

void cmdAdd(Stream& out, const char* arg) {
  if (cfg.count >= MAX_RULES) { out.println(F("Нет места, удалите правило (DEL n)")); return; }
  Rule r;
  if (!parseRule(out, arg, r)) return;
  cfg.rules[cfg.count++] = r;
  saveConfig();
  out.println(F("Добавлено."));
  printRules(out);
  evaluate();
}

void cmdEdit(Stream& out, const char* arg) {
  int n = atoi(arg);
  const char* rest = strchr(arg, ' ');
  if (n < 1 || n > cfg.count || !rest) { out.println(F("Формат: EDIT n 08:00 23:00 [12345]")); return; }
  Rule r;
  if (!parseRule(out, rest + 1, r)) return;
  r.en = cfg.rules[n - 1].en;
  cfg.rules[n - 1] = r;
  saveConfig();
  out.println(F("Изменено."));
  printRules(out);
  evaluate();
}

void cmdEn(Stream& out, const char* arg) {
  int n = 0, v = -1;
  sscanf(arg, "%d %d", &n, &v);
  if (n < 1 || n > cfg.count || (v != 0 && v != 1)) { out.println(F("Формат: EN n 0|1")); return; }
  cfg.rules[n - 1].en = v;
  saveConfig();
  printRules(out);
  evaluate();
}

void cmdDel(Stream& out, const char* arg) {
  int n = atoi(arg);
  if (n < 1 || n > cfg.count) { out.println(F("Нет такого правила. LIST — список")); return; }
  for (uint8_t i = n - 1; i + 1 < cfg.count; i++) cfg.rules[i] = cfg.rules[i + 1];
  cfg.count--;
  saveConfig();
  out.println(F("Удалено."));
  printRules(out);
  evaluate();
}

void handleCommand(Stream& out, char* line) {
  toUpper(line);
  while (*line == ' ') line++;
  bool machine = false;
  if (*line == '!') {  // команда от приложения
    machine = true;
    line++;
    if (&out == (Stream*)&bt) btMachine = true;
  }
  Stream& o = machine ? (Stream&)nullOut : out;
  char* arg = strchr(line, ' ');
  if (arg) { *arg++ = 0; while (*arg == ' ') arg++; } else arg = line + strlen(line);

  if (!*line) { /* пустая команда — у приложения это просто запрос состояния */ }
  else if (!strcmp(line, "HELP") || !strcmp(line, "?")) printHelp(o);
  else if (!strcmp(line, "STATUS") || !strcmp(line, "S")) printStatus(o);
  else if (!strcmp(line, "GET")) { if (!machine) { evaluate(); printMachine(out); } }
  else if (!strcmp(line, "TIME")) cmdTime(o, arg);
  else if (!strcmp(line, "ADD")) cmdAdd(o, arg);
  else if (!strcmp(line, "EDIT")) cmdEdit(o, arg);
  else if (!strcmp(line, "EN")) cmdEn(o, arg);
  else if (!strcmp(line, "LIST")) printRules(o);
  else if (!strcmp(line, "DEL")) cmdDel(o, arg);
  else if (!strcmp(line, "CLEAR")) { cfg.count = 0; saveConfig(); o.println(F("Все правила удалены.")); evaluate(); }
  else if (!strcmp(line, "ON"))  { overrideState = 1; evaluate(); printStatus(o); }
  else if (!strcmp(line, "OFF")) { overrideState = 0; evaluate(); printStatus(o); }
  else if (!strcmp(line, "AUTO")) { overrideState = -1; evaluate(); printStatus(o); }
  else { o.print(F("Неизвестная команда: ")); o.println(line); o.println(F("HELP — список команд")); }

  if (machine) {
    evaluate();
    printMachine(out);
  }
}

const uint8_t LINE_MAX = 48;
char usbLine[LINE_MAX];
uint8_t usbLen = 0;
char btLine[LINE_MAX];
uint8_t btLen = 0;

void pollStream(Stream& s, char* buf, uint8_t& len) {
  while (s.available()) {
    char c = s.read();
    if (c == '\n' || c == '\r') {
      if (len) {
        buf[len] = 0;
        handleCommand(s, buf);
        len = 0;
      }
    } else if (len < LINE_MAX - 1) {
      buf[len++] = c;
    }
  }
}

// ================= Arduino =================
unsigned long lastTick = 0;

void setup() {
  digitalWrite(PIN_RELAY, RELAY_ACTIVE_HIGH ? LOW : HIGH);  // реле выключено с самого старта
  pinMode(PIN_RELAY, OUTPUT);
  pinMode(PIN_LED, OUTPUT);

  Serial.begin(9600);
  bt.begin(BT_BAUD);

  loadConfig();
  rtcInit();
  evaluate();  // сразу восстановить положение реле по расписанию

  Serial.println(F("Таймер реле запущен. HELP — список команд"));
  printStatus(Serial);
}

void loop() {
  pollStream(Serial, usbLine, usbLen);
  pollStream(bt, btLine, btLen);
  if (millis() - lastTick >= 1000) {
    lastTick = millis();
    evaluate();
  }
}
