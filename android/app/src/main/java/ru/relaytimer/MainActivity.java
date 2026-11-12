package ru.relaytimer;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.app.TimePickerDialog;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothGatt;
import android.bluetooth.BluetoothGattCallback;
import android.bluetooth.BluetoothGattCharacteristic;
import android.bluetooth.BluetoothGattDescriptor;
import android.bluetooth.BluetoothGattService;
import android.bluetooth.BluetoothProfile;
import android.bluetooth.BluetoothManager;
import android.bluetooth.BluetoothSocket;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.content.pm.PackageManager;
import android.content.res.ColorStateList;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.Drawable;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.RippleDrawable;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.os.SystemClock;
import android.provider.Settings;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.Switch;
import android.widget.TextView;
import android.widget.Toast;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.util.Arrays;
import java.io.Closeable;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.UUID;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.Semaphore;
import java.util.concurrent.TimeUnit;

/**
 * Таймер света: управление реле на Arduino (HC-06) по расписанию.
 * Протокол: приложение шлёт команды с «!», Arduino отвечает строками #S / #R / #E.
 */
@SuppressLint({"MissingPermission", "SetTextI18n"})
public class MainActivity extends Activity {

    private static final UUID SPP = UUID.fromString("00001101-0000-1000-8000-00805F9B34FB");
    private static final int REQ_BT = 1;
    private static final int MAX_RULES = 8;
    private static final String[] DAY_SHORT = {"Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"};
    private static final Locale RU = new Locale("ru", "RU");

    private static final int C_BG = 0xFFEEF1F5;
    private static final int C_CARD = 0xFFFFFFFF;
    private static final int C_SOFT = 0xFFF1F3F6;
    private static final int C_TEXT = 0xFF1F2937;
    private static final int C_MUTED = 0xFF6B7280;
    private static final int C_ACCENT = 0xFF1E88E5;
    private static final int C_LIGHT_ON = 0xFFFFC107;
    private static final int C_LIGHT_OFF = 0xFFB0B7C3;
    private static final int C_RED = 0xFFE53935;
    private static final int C_GREEN = 0xFF43A047;
    private static final int C_AMBER_TEXT = 0xFFB26A00;

    static class Rule {
        int onH, onM, offH, offM, days;
        boolean en;

        Rule(int onH, int onM, int offH, int offM, int days, boolean en) {
            this.onH = onH;
            this.onM = onM;
            this.offH = offH;
            this.offM = offM;
            this.days = days;
            this.en = en;
        }

        Rule copy() {
            return new Rule(onH, onM, offH, offM, days, en);
        }

        String sig() {
            return onH + ":" + onM + "-" + offH + ":" + offM + "/" + days + "/" + en;
        }
    }

    private final Handler ui = new Handler(Looper.getMainLooper());
    private SharedPreferences prefs;

    // ---- соединение ----
    private BleConnection ble;
    private volatile BluetoothSocket socket;
    private volatile int connGen = 0;
    private volatile boolean connected = false;
    private boolean connecting = false;
    private String connName = "";
    private final LinkedBlockingQueue<String> queue = new LinkedBlockingQueue<>();
    private final Semaphore ack = new Semaphore(0);

    // ---- состояние устройства ----
    private boolean haveState = false;
    private boolean timeSet = false;
    private boolean relayOn = false;
    private int override = -1;
    private long devTimeMs = 0;
    private long devRxElapsed = 0;
    private List<Rule> rules = new ArrayList<>();
    private List<Rule> pendingRules = null;
    private String rulesSig = null;
    private boolean autoSyncDone = false;

    private final SimpleDateFormat parseFmt = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US);
    private final SimpleDateFormat timeFmt = new SimpleDateFormat("HH:mm:ss", Locale.US);
    private final SimpleDateFormat dateFmt = new SimpleDateFormat("EEEE, d MMMM yyyy", RU);

    // ---- элементы экрана ----
    private TextView connDot, connText, relayCircle, relayMode, nextText, devTime, devDate, devDiff;
    private Button connBtn, btnOn, btnOff, btnAuto, addBtn;
    private LinearLayout rulesBox;
    private int tickCount = 0;

    // =====================================================================
    // Жизненный цикл
    // =====================================================================

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        parseFmt.setLenient(false);
        prefs = getSharedPreferences("relay_timer", Context.MODE_PRIVATE);
        buildUi();
        setConnStatus("Не подключено", C_LIGHT_OFF);
        refreshAll();
        if (ensurePermission()) autoConnect();
        ui.post(tick);
    }

    @Override
    protected void onDestroy() {
        ui.removeCallbacks(tick);
        disconnect();
        super.onDestroy();
    }

    private final Runnable tick = new Runnable() {
        @Override
        public void run() {
            updateClock();
            tickCount++;
            if (connected && tickCount % 3 == 0 && queue.isEmpty()) queue.offer("!GET");
            ui.postDelayed(this, 1000);
        }
    };

    // =====================================================================
    // Разрешения и выбор устройства
    // =====================================================================

    private boolean ensurePermission() {
        if (Build.VERSION.SDK_INT >= 31
                && checkSelfPermission(Manifest.permission.BLUETOOTH_CONNECT) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[]{Manifest.permission.BLUETOOTH_CONNECT}, REQ_BT);
            return false;
        }
        return true;
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (requestCode != REQ_BT) return;
        if (grantResults.length > 0 && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
            autoConnect();
        } else {
            toast("Без разрешения «Устройства поблизости» приложение не сможет подключиться");
        }
    }

    private BluetoothAdapter adapter() {
        BluetoothManager bm = (BluetoothManager) getSystemService(Context.BLUETOOTH_SERVICE);
        return bm != null ? bm.getAdapter() : null;
    }

    private void autoConnect() {
        String addr = prefs.getString("addr", null);
        BluetoothAdapter ad = adapter();
        if (addr == null || ad == null || !ad.isEnabled()) return;
        try {
            connect(ad.getRemoteDevice(addr));
        } catch (IllegalArgumentException ignored) {
        }
    }

    private void onConnButton() {
        if (connected || connecting) {
            disconnect();
            setConnStatus("Не подключено", C_LIGHT_OFF);
        } else {
            chooseDevice();
        }
    }

    private void chooseDevice() {
        if (!ensurePermission()) return;
        BluetoothAdapter ad = adapter();
        if (ad == null) {
            toast("На телефоне нет Bluetooth");
            return;
        }
        if (!ad.isEnabled()) {
            startActivity(new Intent(BluetoothAdapter.ACTION_REQUEST_ENABLE));
            return;
        }
        final List<BluetoothDevice> list = new ArrayList<>(ad.getBondedDevices());
        if (list.isEmpty()) {
            new AlertDialog.Builder(this)
                    .setTitle("Нет сопряжённых устройств")
                    .setMessage("Откройте настройки Bluetooth, найдите HC-06 и выполните сопряжение "
                            + "(PIN-код 1234 или 0000). Затем вернитесь в приложение.")
                    .setPositiveButton("Открыть настройки",
                            (d, w) -> startActivity(new Intent(Settings.ACTION_BLUETOOTH_SETTINGS)))
                    .setNegativeButton("Отмена", null)
                    .show();
            return;
        }
        String[] names = new String[list.size()];
        for (int i = 0; i < list.size(); i++) {
            String n = list.get(i).getName();
            names[i] = (n == null ? "Без имени" : n) + "\n" + list.get(i).getAddress();
        }
        new AlertDialog.Builder(this)
                .setTitle("Выберите модуль (обычно HC-06)")
                .setItems(names, (d, w) -> {
                    BluetoothDevice dev = list.get(w);
                    prefs.edit().putString("addr", dev.getAddress()).apply();
                    connect(dev);
                })
                .setNeutralButton("Сопрячь новое…",
                        (d, w) -> startActivity(new Intent(Settings.ACTION_BLUETOOTH_SETTINGS)))
                .show();
    }

    // =====================================================================
    // Bluetooth-соединение
    // =====================================================================

    private void connect(final BluetoothDevice dev) {
        disconnect();
        final int gen = ++connGen;
        String n = dev.getName();
        connName = n == null ? dev.getAddress() : n;
        connecting = true;
        setConnStatus("Подключение к " + connName + "…", C_LIGHT_ON);
        connBtn.setText("Отмена");
        if (dev.getType() == BluetoothDevice.DEVICE_TYPE_LE) {
            connectBle(gen, dev, null);
        } else {
            new Thread(() -> runConnection(gen, dev)).start();
        }
    }

    private void runConnection(final int gen, BluetoothDevice dev) {
        final BluetoothSocket s;
        try {
            s = openSocket(gen, dev);
        } catch (IOException | SecurityException e) {
            ui.post(() -> {
                if (gen != connGen) return;
                if (dev.getType() == BluetoothDevice.DEVICE_TYPE_CLASSIC || e instanceof SecurityException) {
                    showConnectionError(e.toString());
                } else {
                    connectBle(gen, dev, e.toString());
                }
            });
            return;
        }
        if (s == null || gen != connGen) {
            closeQuietly(s);
            return;
        }
        final OutputStream out;
        final InputStream in;
        try {
            out = s.getOutputStream();
            in = s.getInputStream();
        } catch (IOException e) {
            closeQuietly(s);
            ui.post(() -> {
                if (gen == connGen) {
                    connecting = false;
                    connBtn.setText("Подключить");
                    setConnStatus("Ошибка соединения", C_RED);
                }
            });
            return;
        }
        socket = s;
        queue.clear();
        ui.post(() -> {
            if (gen == connGen) onConnected();
        });
        new Thread(() -> writerLoop(gen, out)).start();
        readLoop(gen, in);
    }

    private BluetoothSocket openSocket(int gen, BluetoothDevice dev) throws IOException {
        StringBuilder errors = new StringBuilder();
        String[] modes = {"SPP", "SPP без аутентификации", "RFCOMM, канал 1"};
        for (int attempt = 0; attempt < modes.length && gen == connGen; attempt++) {
            BluetoothSocket candidate = null;
            boolean opened = false;
            try {
                switch (attempt) {
                    case 0:
                        candidate = dev.createRfcommSocketToServiceRecord(SPP);
                        break;
                    case 1:
                        candidate = dev.createInsecureRfcommSocketToServiceRecord(SPP);
                        break;
                    default:
                        Method method = dev.getClass().getMethod("createRfcommSocket", int.class);
                        candidate = (BluetoothSocket) method.invoke(dev, 1);
                        break;
                }
                if (candidate == null) throw new IOException("Сокет не создан");
                if (gen != connGen) return null;
                candidate.connect();
                opened = true;
                return candidate;
            } catch (IOException | ReflectiveOperationException e) {
                Throwable cause = e instanceof java.lang.reflect.InvocationTargetException
                        && e.getCause() != null ? e.getCause() : e;
                if (errors.length() > 0) errors.append('\n');
                errors.append(modes[attempt]).append(": ").append(cause);
            } finally {
                if (!opened) closeQuietly(candidate);
            }
        }
        if (gen != connGen) return null;
        throw new IOException(errors.toString());
    }

    private void writerLoop(int gen, OutputStream out) {
        try {
            while (gen == connGen) {
                String cmd = queue.poll(1, TimeUnit.SECONDS);
                if (cmd == null) continue;
                ack.drainPermits();
                out.write((cmd + "\n").getBytes(StandardCharsets.UTF_8));
                out.flush();
                // ждём конца ответа, чтобы не говорить одновременно с Arduino
                ack.tryAcquire(3, TimeUnit.SECONDS);
            }
        } catch (IOException | SecurityException e) {
            ui.post(() -> {
                if (gen == connGen && ble != null) ble.fail(e.getMessage());
            });
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    private void readLoop(final int gen, InputStream in) {
        try {
            BufferedReader r = new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8));
            String line;
            while ((line = r.readLine()) != null) {
                receiveLine(gen, line);
            }
        } catch (IOException ignored) {
        }
        ui.post(() -> {
            if (gen == connGen) onConnectionLost();
        });
    }

    private void receiveLine(int gen, String line) {
        if (gen != connGen) return;
        int start = line.indexOf('#');
        if (start < 0) return;
        String message = line.substring(start).trim();
        if (message.equals("#E")) ack.release();
        ui.post(() -> {
            if (gen == connGen) handleLine(message);
        });
    }

    private void showConnectionError(String message) {
        disconnect();
        setConnStatus("Не удалось подключиться к " + connName, C_RED);
        new AlertDialog.Builder(this)
                .setTitle("Ошибка Bluetooth")
                .setMessage(message)
                .setPositiveButton("OK", null)
                .show();
    }

    private static UUID bleUuid(String shortId) {
        return UUID.fromString("0000" + shortId + "-0000-1000-8000-00805f9b34fb");
    }

    private void connectBle(int gen, BluetoothDevice dev, String classicError) {
        ble = new BleConnection(gen, classicError);
        try {
            ble.gatt = dev.connectGatt(this, false, ble, BluetoothDevice.TRANSPORT_LE);
            if (ble.gatt == null) {
                ble.fail("Android не открыл GATT");
                return;
            }
            ui.postDelayed(ble.timeout, 12000);
        } catch (SecurityException e) {
            ble.fail(e.toString());
        }
    }

    private final class BleConnection extends BluetoothGattCallback {
        private final int gen;
        private final String classicError;
        private final Runnable timeout = () -> fail("истекло время настройки GATT");
        private final Semaphore writeDone = new Semaphore(0);
        private final ByteArrayOutputStream line = new ByteArrayOutputStream();
        private BluetoothGatt gatt;
        private BluetoothGattCharacteristic tx;
        private volatile int writeStatus;
        private boolean dropLine;

        BleConnection(int gen, String classicError) {
            this.gen = gen;
            this.classicError = classicError;
        }

        @Override
        public void onConnectionStateChange(BluetoothGatt client, int status, int state) {
            ui.post(() -> {
                if (ble != this) return;
                if (status != BluetoothGatt.GATT_SUCCESS || state == BluetoothProfile.STATE_DISCONNECTED) {
                    fail("GATT отключён, код " + status);
                } else if (state == BluetoothProfile.STATE_CONNECTED && !client.discoverServices()) {
                    fail("не удалось запустить поиск сервисов");
                }
            });
        }

        @Override
        public void onServicesDiscovered(BluetoothGatt client, int status) {
            ui.post(() -> {
                if (ble != this) return;
                if (status != BluetoothGatt.GATT_SUCCESS) {
                    fail("поиск сервисов, код " + status);
                    return;
                }
                BluetoothGattService service = client.getService(bleUuid("ffe0"));
                BluetoothGattCharacteristic rx = service == null ? null : service.getCharacteristic(bleUuid("ffe1"));
                tx = service == null ? null : service.getCharacteristic(bleUuid("ffe2"));
                if (rx == null || tx == null
                        || (rx.getProperties() & BluetoothGattCharacteristic.PROPERTY_NOTIFY) == 0
                        || (tx.getProperties() & BluetoothGattCharacteristic.PROPERTY_WRITE) == 0) {
                    fail("не найден интерфейс FFE0/FFE1/FFE2");
                    return;
                }
                BluetoothGattDescriptor cccd = rx.getDescriptor(bleUuid("2902"));
                if (cccd == null || !client.setCharacteristicNotification(rx, true)
                        || !enableNotifications(client, cccd)) {
                    fail("не удалось включить уведомления FFE1");
                }
            });
        }

        @SuppressWarnings("deprecation")
        private boolean enableNotifications(BluetoothGatt client, BluetoothGattDescriptor cccd) {
            byte[] value = BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE;
            if (Build.VERSION.SDK_INT >= 33) return client.writeDescriptor(cccd, value) == 0;
            return cccd.setValue(value) && client.writeDescriptor(cccd);
        }

        @Override
        public void onDescriptorWrite(BluetoothGatt client, BluetoothGattDescriptor descriptor, int status) {
            ui.post(() -> {
                if (ble != this || !connecting) return;
                if (status != BluetoothGatt.GATT_SUCCESS) {
                    fail("подписка FFE1, код " + status);
                    return;
                }
                ui.removeCallbacks(timeout);
                onConnected();
                new Thread(() -> writerLoop(gen, new OutputStream() {
                    @Override
                    public void write(int value) throws IOException {
                        write(new byte[]{(byte) value});
                    }

                    @Override
                    public void write(byte[] bytes) throws IOException {
                        writeCommand(client, bytes);
                    }
                })).start();
            });
        }

        @SuppressWarnings("deprecation")
        private void writeCommand(BluetoothGatt client, byte[] bytes) throws IOException {
            for (int offset = 0; offset < bytes.length; offset += 20) {
                byte[] chunk = Arrays.copyOfRange(bytes, offset, Math.min(bytes.length, offset + 20));
                if (gen != connGen) throw new IOException("BLE отключён");
                writeDone.drainPermits();
                int type = BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT;
                boolean started;
                if (Build.VERSION.SDK_INT >= 33) {
                    started = client.writeCharacteristic(tx, chunk, type) == 0;
                } else {
                    tx.setWriteType(type);
                    started = tx.setValue(chunk) && client.writeCharacteristic(tx);
                }
                try {
                    if (!started || !writeDone.tryAcquire(4, TimeUnit.SECONDS)
                            || writeStatus != BluetoothGatt.GATT_SUCCESS) {
                        throw new IOException("не удалось записать данные в FFE2");
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new IOException(e);
                }
            }
        }

        @Override
        public void onCharacteristicWrite(BluetoothGatt client, BluetoothGattCharacteristic characteristic, int status) {
            writeStatus = status;
            writeDone.release();
        }

        @Override
        public void onCharacteristicChanged(BluetoothGatt client, BluetoothGattCharacteristic characteristic, byte[] value) {
            receiveBytes(value);
        }

        @Override
        @SuppressWarnings("deprecation")
        public void onCharacteristicChanged(BluetoothGatt client, BluetoothGattCharacteristic characteristic) {
            receiveBytes(characteristic.getValue());
        }

        private synchronized void receiveBytes(byte[] value) {
            if (gen != connGen || value == null) return;
            for (byte b : value) {
                if (b == 10 || b == 13) {
                    if (!dropLine && line.size() > 0) {
                        receiveLine(gen, new String(line.toByteArray(), StandardCharsets.UTF_8));
                    }
                    line.reset();
                    dropLine = false;
                } else if (line.size() == 512) {
                    dropLine = true;
                } else {
                    line.write(b);
                }
            }
        }

        private void fail(String detail) {
            if (ble != this) return;
            String message = "BLE: " + detail;
            showConnectionError(classicError == null ? message : message + "\n" + classicError);
        }

        private void close() {
            ui.removeCallbacks(timeout);
            if (gatt != null) gatt.close();
        }
    }

    private void onConnected() {
        connecting = false;
        connected = true;
        autoSyncDone = false;
        setConnStatus("Подключено: " + connName, C_GREEN);
        connBtn.setText("Отключить");
        queue.offer("!GET");
    }

    private void onConnectionLost() {
        connected = false;
        connecting = false;
        closeQuietly(socket);
        socket = null;
        setConnStatus("Связь потеряна. Нажмите «Подключить»", C_RED);
        connBtn.setText("Подключить");
        refreshAll();
    }

    private void disconnect() {
        connGen++;
        if (ble != null) {
            BleConnection closing = ble;
            ble = null;
            closing.close();
        }
        connected = false;
        connecting = false;
        closeQuietly(socket);
        socket = null;
        queue.clear();
        ack.release();
        if (connBtn != null) connBtn.setText("Подключить");
    }

    private static void closeQuietly(Closeable c) {
        if (c == null) return;
        try {
            c.close();
        } catch (IOException ignored) {
        }
    }

    private boolean sendCmd(String cmd) {
        if (!connected) {
            toast("Нет подключения к устройству");
            return false;
        }
        queue.offer(cmd);
        return true;
    }

    // =====================================================================
    // Разбор ответов Arduino
    // =====================================================================

    private void handleLine(String l) {
        String[] p = l.split("\\s+");
        switch (p[0]) {
            case "#S":
                if (p.length < 6) return;
                timeSet = p[1].equals("1");
                try {
                    Date d = parseFmt.parse(p[2] + " " + p[3]);
                    if (d != null) {
                        devTimeMs = d.getTime();
                        devRxElapsed = SystemClock.elapsedRealtime();
                    }
                } catch (ParseException e) {
                    if (timeSet) timeSet = false;
                }
                relayOn = p[4].equals("1");
                override = parseIntOr(p[5], -1);
                haveState = true;
                pendingRules = new ArrayList<>();
                break;
            case "#R":
                if (pendingRules == null || p.length < 6) return;
                int[] a = parseHM(p[2]);
                int[] b = parseHM(p[3]);
                if (a == null || b == null) return;
                pendingRules.add(new Rule(a[0], a[1], b[0], b[1], parseIntOr(p[4], 127), p[5].equals("1")));
                break;
            case "#E":
                if (pendingRules != null) {
                    rules = pendingRules;
                    pendingRules = null;
                }
                refreshAll();
                maybeAutoSync();
                break;
            default:
                break;
        }
    }

    private static int parseIntOr(String s, int def) {
        try {
            return Integer.parseInt(s);
        } catch (NumberFormatException e) {
            return def;
        }
    }

    private static int[] parseHM(String s) {
        String[] x = s.split(":");
        if (x.length != 2) return null;
        int h = parseIntOr(x[0], -1);
        int m = parseIntOr(x[1], -1);
        if (h < 0 || h > 23 || m < 0 || m > 59) return null;
        return new int[]{h, m};
    }

    // =====================================================================
    // Время
    // =====================================================================

    private long devNow() {
        return devTimeMs + (SystemClock.elapsedRealtime() - devRxElapsed);
    }

    private void syncTime() {
        SimpleDateFormat f = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US);
        if (sendCmd("!TIME " + f.format(new Date()))) toast("Время на устройстве синхронизировано с телефоном");
    }

    private void maybeAutoSync() {
        if (autoSyncDone || !haveState || !connected) return;
        autoSyncDone = true;
        long diff = Math.abs(System.currentTimeMillis() - devNow());
        if (!timeSet || diff > 5000) syncTime();
    }

    private static String fmtDur(long sec) {
        if (sec < 60) return sec + " с";
        if (sec < 3600) return (sec / 60) + " мин " + (sec % 60) + " с";
        if (sec < 86400) return (sec / 3600) + " ч " + (sec % 3600 / 60) + " мин";
        return (sec / 86400) + " дн";
    }

    private void updateClock() {
        if (!haveState) {
            devTime.setText("--:--:--");
            devDate.setText(connected ? "Получение данных…" : "Нет данных — подключитесь к устройству");
            devDiff.setText("");
            nextText.setText("");
            return;
        }
        if (!timeSet) {
            devTime.setText("--:--:--");
            devDate.setText("Время на устройстве не установлено");
            devDiff.setText("Нажмите «Синхронизировать с телефоном»");
            devDiff.setTextColor(C_RED);
            nextText.setText("");
            return;
        }
        long t = devNow();
        Date d = new Date(t);
        devTime.setText(timeFmt.format(d));
        String ds = dateFmt.format(d);
        devDate.setText(ds.isEmpty() ? ds : Character.toUpperCase(ds.charAt(0)) + ds.substring(1));
        long diff = (System.currentTimeMillis() - t) / 1000;
        if (Math.abs(diff) < 3) {
            devDiff.setText("Совпадает с часами телефона");
            devDiff.setTextColor(C_GREEN);
        } else {
            devDiff.setText((diff > 0 ? "Отстаёт на " : "Спешит на ") + fmtDur(Math.abs(diff)));
            devDiff.setTextColor(Math.abs(diff) > 60 ? C_RED : C_AMBER_TEXT);
        }
        nextText.setText(nextSwitchText(t));
    }

    // ---- расписание, та же логика, что в Arduino ----

    private static boolean dayIn(int mask, int dow) {
        return (mask & (1 << (dow - 1))) != 0;
    }

    private boolean autoAt(int dow, int min) {
        int yest = dow == 1 ? 7 : dow - 1;
        for (Rule r : rules) {
            if (!r.en) continue;
            int on = r.onH * 60 + r.onM;
            int off = r.offH * 60 + r.offM;
            if (on < off) {
                if (dayIn(r.days, dow) && min >= on && min < off) return true;
            } else if ((min >= on && dayIn(r.days, dow)) || (min < off && dayIn(r.days, yest))) {
                return true;
            }
        }
        return false;
    }

    private String nextSwitchText(long t) {
        boolean any = false;
        for (Rule r : rules) any |= r.en && r.days != 0;
        if (!any) return "Нет действующих правил";
        Calendar c = Calendar.getInstance();
        c.setTimeInMillis(t);
        int dow = ((c.get(Calendar.DAY_OF_WEEK) + 5) % 7) + 1; // 1 = Пн ... 7 = Вс
        int min = c.get(Calendar.HOUR_OF_DAY) * 60 + c.get(Calendar.MINUTE);
        boolean cur = autoAt(dow, min);
        int d = dow, m = min;
        for (int step = 1; step <= 7 * 1440; step++) {
            m++;
            if (m == 1440) {
                m = 0;
                d = d == 7 ? 1 : d + 1;
            }
            if (autoAt(d, m) != cur) {
                int days = (min + step) / 1440;
                String when = days == 0 ? "сегодня" : days == 1 ? "завтра" : DAY_SHORT[d - 1];
                return "Далее по расписанию: " + (cur ? "выключение " : "включение ")
                        + when + " в " + hm(m / 60, m % 60);
            }
        }
        return cur ? "По расписанию свет горит постоянно" : "";
    }

    // =====================================================================
    // Экран
    // =====================================================================

    private void buildUi() {
        ScrollView sv = new ScrollView(this);
        sv.setFillViewport(true);
        sv.setBackgroundColor(C_BG);
        LinearLayout main = vertical();
        main.setPadding(dp(12), dp(12), dp(12), dp(24));
        sv.addView(main, new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT));

        // --- подключение ---
        LinearLayout c1 = card(main);
        LinearLayout row = horizontal();
        row.setGravity(Gravity.CENTER_VERTICAL);
        connDot = new TextView(this);
        LinearLayout.LayoutParams dotLp = new LinearLayout.LayoutParams(dp(12), dp(12));
        dotLp.rightMargin = dp(10);
        row.addView(connDot, dotLp);
        connText = text("", 15, C_TEXT, false);
        row.addView(connText, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
        connBtn = button("Подключить", C_ACCENT, Color.WHITE);
        connBtn.setOnClickListener(v -> onConnButton());
        LinearLayout.LayoutParams cbLp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT,
                ViewGroup.LayoutParams.WRAP_CONTENT);
        cbLp.leftMargin = dp(8);
        row.addView(connBtn, cbLp);
        c1.addView(row);

        // --- свет ---
        LinearLayout c2 = card(main);
        c2.addView(title("Свет"));
        relayCircle = text("—", 30, Color.WHITE, true);
        relayCircle.setGravity(Gravity.CENTER);
        LinearLayout.LayoutParams rcLp = new LinearLayout.LayoutParams(dp(150), dp(150));
        rcLp.gravity = Gravity.CENTER_HORIZONTAL;
        rcLp.topMargin = dp(8);
        rcLp.bottomMargin = dp(10);
        c2.addView(relayCircle, rcLp);
        relayMode = text("", 15, C_TEXT, false);
        relayMode.setGravity(Gravity.CENTER);
        c2.addView(relayMode, matchWrap());
        nextText = text("", 14, C_MUTED, false);
        nextText.setGravity(Gravity.CENTER);
        LinearLayout.LayoutParams ntLp = matchWrap();
        ntLp.topMargin = dp(4);
        c2.addView(nextText, ntLp);
        LinearLayout btnRow = horizontal();
        btnOn = button("Включить", C_SOFT, C_TEXT);
        btnOff = button("Выключить", C_SOFT, C_TEXT);
        btnAuto = button("Авто", C_SOFT, C_TEXT);
        btnOn.setOnClickListener(v -> sendCmd("!ON"));
        btnOff.setOnClickListener(v -> sendCmd("!OFF"));
        btnAuto.setOnClickListener(v -> sendCmd("!AUTO"));
        for (Button b : new Button[]{btnOn, btnOff, btnAuto}) {
            b.setPadding(dp(4), dp(8), dp(4), dp(8));
            b.setTextSize(TypedValue.COMPLEX_UNIT_SP, 15);
            b.setSingleLine(true);
        }
        btnRow.addView(btnOn, weighted(0));
        btnRow.addView(btnOff, weighted(8));
        btnRow.addView(btnAuto, weighted(8));
        LinearLayout.LayoutParams brLp = matchWrap();
        brLp.topMargin = dp(14);
        c2.addView(btnRow, brLp);
        TextView hint1 = text("«Включить»/«Выключить» действуют до следующего переключения по расписанию, "
                + "«Авто» — сразу вернуться к расписанию.", 12, C_MUTED, false);
        LinearLayout.LayoutParams h1Lp = matchWrap();
        h1Lp.topMargin = dp(8);
        c2.addView(hint1, h1Lp);

        // --- часы ---
        LinearLayout c3 = card(main);
        c3.addView(title("Часы устройства"));
        devTime = text("--:--:--", 44, C_TEXT, true);
        devTime.setGravity(Gravity.CENTER);
        c3.addView(devTime, matchWrap());
        devDate = text("", 15, C_TEXT, false);
        devDate.setGravity(Gravity.CENTER);
        c3.addView(devDate, matchWrap());
        devDiff = text("", 14, C_MUTED, false);
        devDiff.setGravity(Gravity.CENTER);
        LinearLayout.LayoutParams ddLp = matchWrap();
        ddLp.topMargin = dp(4);
        c3.addView(devDiff, ddLp);
        Button syncBtn = button("Синхронизировать с телефоном", C_ACCENT, Color.WHITE);
        syncBtn.setOnClickListener(v -> syncTime());
        LinearLayout.LayoutParams sbLp = matchWrap();
        sbLp.topMargin = dp(12);
        c3.addView(syncBtn, sbLp);

        // --- расписание ---
        LinearLayout c4 = card(main);
        c4.addView(title("Расписание"));
        c4.addView(text("Нажмите на правило, чтобы изменить. Удерживайте — чтобы удалить.", 13, C_MUTED, false));
        rulesBox = vertical();
        c4.addView(rulesBox, matchWrap());
        addBtn = button("+  Добавить правило", C_ACCENT, Color.WHITE);
        addBtn.setOnClickListener(v -> editRule(-1));
        LinearLayout.LayoutParams abLp = matchWrap();
        abLp.topMargin = dp(14);
        c4.addView(addBtn, abLp);

        setContentView(sv);
    }

    private void setConnStatus(String s, int color) {
        connText.setText(s);
        connDot.setBackground(oval(color));
    }

    private void refreshAll() {
        // свет
        if (!haveState) {
            relayCircle.setText("?");
            relayCircle.setBackground(oval(C_LIGHT_OFF));
            relayCircle.setTextColor(Color.WHITE);
            relayMode.setText("Состояние неизвестно");
        } else {
            relayCircle.setText(relayOn ? "ВКЛ" : "ВЫКЛ");
            relayCircle.setBackground(oval(relayOn ? C_LIGHT_ON : C_LIGHT_OFF));
            relayCircle.setTextColor(relayOn ? 0xFF4E3B00 : Color.WHITE);
            relayMode.setText(override >= 0
                    ? "Ручной режим (до следующего переключения)"
                    : "Работает по расписанию");
        }
        styleToggle(btnOn, haveState && override == 1);
        styleToggle(btnOff, haveState && override == 0);
        styleToggle(btnAuto, haveState && override < 0);

        // правила — перестраиваем только при изменениях
        StringBuilder sb = new StringBuilder(haveState ? "S" : "N");
        for (Rule r : rules) sb.append('|').append(r.sig());
        String sig = sb.toString();
        if (!sig.equals(rulesSig)) {
            rulesSig = sig;
            rebuildRules();
        }
        updateClock();
    }

    private void rebuildRules() {
        rulesBox.removeAllViews();
        if (rules.isEmpty()) {
            TextView empty = text(haveState
                    ? "Правил пока нет. Нажмите «Добавить правило»."
                    : "Подключитесь к устройству, чтобы увидеть расписание.", 15, C_MUTED, false);
            empty.setGravity(Gravity.CENTER);
            LinearLayout.LayoutParams lp = matchWrap();
            lp.topMargin = dp(16);
            lp.bottomMargin = dp(4);
            rulesBox.addView(empty, lp);
        }
        for (int i = 0; i < rules.size(); i++) rulesBox.addView(ruleCard(i, rules.get(i)));
        addBtn.setVisibility(rules.size() < MAX_RULES ? View.VISIBLE : View.GONE);
    }

    private View ruleCard(final int idx, Rule r) {
        LinearLayout row = horizontal();
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setBackground(ripple(C_SOFT, 14));
        row.setPadding(dp(16), dp(12), dp(8), dp(12));
        LinearLayout.LayoutParams lp = matchWrap();
        lp.topMargin = dp(10);
        row.setLayoutParams(lp);

        LinearLayout col = vertical();
        boolean overnight = r.onH * 60 + r.onM > r.offH * 60 + r.offM;
        col.addView(text(hm(r.onH, r.onM) + "  →  " + hm(r.offH, r.offM), 26, C_TEXT, true));
        col.addView(text(daysText(r.days) + (overnight ? " · выкл. на следующий день" : ""), 14, C_MUTED, false));
        row.addView(col, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));

        Switch sw = new Switch(this);
        sw.setChecked(r.en);
        sw.setOnCheckedChangeListener((b, on) -> {
            if (!sendCmd("!EN " + (idx + 1) + " " + (on ? 1 : 0))) {
                rulesSig = null;
                ui.post(this::refreshAll);
            }
        });
        row.addView(sw);

        row.setAlpha(r.en ? 1f : 0.5f);
        row.setOnClickListener(v -> editRule(idx));
        row.setOnLongClickListener(v -> {
            confirmDelete(idx);
            return true;
        });
        return row;
    }

    private void confirmDelete(final int idx) {
        if (idx < 0 || idx >= rules.size()) return;
        Rule r = rules.get(idx);
        new AlertDialog.Builder(this)
                .setTitle("Удалить правило?")
                .setMessage(hm(r.onH, r.onM) + " → " + hm(r.offH, r.offM) + ", " + daysText(r.days))
                .setPositiveButton("Удалить", (d, w) -> sendCmd("!DEL " + (idx + 1)))
                .setNegativeButton("Отмена", null)
                .show();
    }

    // ---- окно правила ----

    private void editRule(final int index) {
        if (!connected) {
            toast("Нет подключения к устройству");
            return;
        }
        if (index < 0 && rules.size() >= MAX_RULES) {
            toast("Можно не больше " + MAX_RULES + " правил");
            return;
        }
        if (index >= rules.size()) return;
        final Rule r = index >= 0 ? rules.get(index).copy() : new Rule(18, 0, 23, 0, 0x7F, true);

        LinearLayout v = vertical();
        v.setPadding(dp(20), dp(8), dp(20), dp(8));

        v.addView(label("Включить в"));
        final Button onB = button("", C_SOFT, C_ACCENT);
        onB.setTextSize(TypedValue.COMPLEX_UNIT_SP, 34);
        onB.setTypeface(Typeface.DEFAULT_BOLD);
        v.addView(onB, matchWrap());

        v.addView(label("Выключить в"));
        final Button offB = button("", C_SOFT, C_ACCENT);
        offB.setTextSize(TypedValue.COMPLEX_UNIT_SP, 34);
        offB.setTypeface(Typeface.DEFAULT_BOLD);
        v.addView(offB, matchWrap());

        final TextView hint = text("", 13, C_MUTED, false);
        LinearLayout.LayoutParams hLp = matchWrap();
        hLp.topMargin = dp(6);
        v.addView(hint, hLp);

        v.addView(label("Дни недели"));
        final TextView[] dayViews = new TextView[7];
        final Runnable upd = () -> {
            onB.setText(hm(r.onH, r.onM));
            offB.setText(hm(r.offH, r.offM));
            int on = r.onH * 60 + r.onM;
            int off = r.offH * 60 + r.offM;
            if (on == off) {
                hint.setText("Время включения и выключения совпадает");
                hint.setTextColor(C_RED);
            } else {
                int dur = off > on ? off - on : 1440 - on + off;
                hint.setText("Свет будет гореть " + (dur / 60) + " ч " + (dur % 60) + " мин"
                        + (off < on ? " — выключится на следующий день" : ""));
                hint.setTextColor(C_MUTED);
            }
            for (int i = 0; i < 7; i++) {
                if (dayViews[i] == null) continue;
                boolean sel = (r.days & (1 << i)) != 0;
                dayViews[i].setBackground(ripple(sel ? C_ACCENT : C_SOFT, 10));
                dayViews[i].setTextColor(sel ? Color.WHITE : C_TEXT);
            }
        };

        LinearLayout daysRow = horizontal();
        for (int i = 0; i < 7; i++) {
            final int bit = 1 << i;
            TextView dv = text(DAY_SHORT[i], 14, C_TEXT, true);
            dv.setGravity(Gravity.CENTER);
            dv.setOnClickListener(x -> {
                r.days ^= bit;
                upd.run();
            });
            LinearLayout.LayoutParams p = new LinearLayout.LayoutParams(0, dp(42), 1f);
            p.leftMargin = i == 0 ? 0 : dp(4);
            daysRow.addView(dv, p);
            dayViews[i] = dv;
        }
        v.addView(daysRow, matchWrap());

        LinearLayout presets = horizontal();
        String[] pNames = {"Каждый день", "Будни", "Выходные"};
        int[] pMasks = {0x7F, 0x1F, 0x60};
        for (int i = 0; i < 3; i++) {
            final int mask = pMasks[i];
            Button pb = button(pNames[i], C_SOFT, C_ACCENT);
            pb.setTextSize(TypedValue.COMPLEX_UNIT_SP, 13);
            pb.setOnClickListener(x -> {
                r.days = mask;
                upd.run();
            });
            presets.addView(pb, weighted(i == 0 ? 0 : 6));
        }
        LinearLayout.LayoutParams prLp = matchWrap();
        prLp.topMargin = dp(8);
        v.addView(presets, prLp);

        onB.setOnClickListener(x -> new TimePickerDialog(this, (tp, h, m) -> {
            r.onH = h;
            r.onM = m;
            upd.run();
        }, r.onH, r.onM, true).show());
        offB.setOnClickListener(x -> new TimePickerDialog(this, (tp, h, m) -> {
            r.offH = h;
            r.offM = m;
            upd.run();
        }, r.offH, r.offM, true).show());
        upd.run();

        ScrollView sv = new ScrollView(this);
        sv.addView(v);

        AlertDialog.Builder bld = new AlertDialog.Builder(this)
                .setTitle(index < 0 ? "Новое правило" : "Правило " + (index + 1))
                .setView(sv)
                .setPositiveButton("Сохранить", null)
                .setNegativeButton("Отмена", null);
        if (index >= 0) bld.setNeutralButton("Удалить", (d, w) -> confirmDelete(index));
        final AlertDialog dlg = bld.create();
        dlg.setOnShowListener(d -> dlg.getButton(AlertDialog.BUTTON_POSITIVE).setOnClickListener(x -> {
            if (r.days == 0) {
                toast("Выберите хотя бы один день");
                return;
            }
            if (r.onH == r.offH && r.onM == r.offM) {
                toast("Время включения и выключения совпадает");
                return;
            }
            String args = hm(r.onH, r.onM) + " " + hm(r.offH, r.offM) + " " + daysDigits(r.days);
            if (sendCmd(index < 0 ? "!ADD " + args : "!EDIT " + (index + 1) + " " + args)) dlg.dismiss();
        }));
        dlg.show();
    }

    // =====================================================================
    // Мелкие помощники
    // =====================================================================

    private static String hm(int h, int m) {
        return String.format(Locale.US, "%02d:%02d", h, m);
    }

    private static String daysDigits(int mask) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 7; i++) if ((mask & (1 << i)) != 0) sb.append(i + 1);
        return sb.toString();
    }

    private static String daysText(int mask) {
        if (mask == 0x7F) return "Каждый день";
        if (mask == 0x1F) return "Будни";
        if (mask == 0x60) return "Выходные";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 7; i++) {
            if ((mask & (1 << i)) != 0) {
                if (sb.length() > 0) sb.append(", ");
                sb.append(DAY_SHORT[i]);
            }
        }
        return sb.length() == 0 ? "Ни одного дня" : sb.toString();
    }

    private void toast(String s) {
        Toast.makeText(this, s, Toast.LENGTH_SHORT).show();
    }

    private int dp(float v) {
        return Math.round(TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, v,
                getResources().getDisplayMetrics()));
    }

    private GradientDrawable round(int color, float radiusDp) {
        GradientDrawable g = new GradientDrawable();
        g.setColor(color);
        g.setCornerRadius(dp(radiusDp));
        return g;
    }

    private Drawable ripple(int color, float radiusDp) {
        return new RippleDrawable(ColorStateList.valueOf(0x22000000), round(color, radiusDp), null);
    }

    private GradientDrawable oval(int color) {
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.OVAL);
        g.setColor(color);
        return g;
    }

    private LinearLayout vertical() {
        LinearLayout l = new LinearLayout(this);
        l.setOrientation(LinearLayout.VERTICAL);
        return l;
    }

    private LinearLayout horizontal() {
        LinearLayout l = new LinearLayout(this);
        l.setOrientation(LinearLayout.HORIZONTAL);
        return l;
    }

    private LinearLayout.LayoutParams matchWrap() {
        return new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT);
    }

    private LinearLayout.LayoutParams weighted(int leftMarginDp) {
        LinearLayout.LayoutParams p = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f);
        p.leftMargin = dp(leftMarginDp);
        return p;
    }

    private LinearLayout card(LinearLayout parent) {
        LinearLayout c = vertical();
        c.setBackground(round(C_CARD, 18));
        c.setPadding(dp(16), dp(16), dp(16), dp(16));
        c.setElevation(dp(1));
        LinearLayout.LayoutParams lp = matchWrap();
        lp.bottomMargin = dp(12);
        parent.addView(c, lp);
        return c;
    }

    private TextView text(String s, float sp, int color, boolean bold) {
        TextView t = new TextView(this);
        t.setText(s);
        t.setTextSize(TypedValue.COMPLEX_UNIT_SP, sp);
        t.setTextColor(color);
        if (bold) t.setTypeface(Typeface.DEFAULT_BOLD);
        return t;
    }

    private TextView title(String s) {
        TextView t = text(s, 18, C_TEXT, true);
        t.setPadding(0, 0, 0, dp(6));
        return t;
    }

    private TextView label(String s) {
        TextView t = text(s, 14, C_MUTED, false);
        t.setPadding(0, dp(12), 0, dp(4));
        return t;
    }

    private Button button(String s, int bg, int fg) {
        Button b = new Button(this);
        b.setText(s);
        b.setAllCaps(false);
        b.setTextSize(TypedValue.COMPLEX_UNIT_SP, 16);
        b.setTextColor(fg);
        b.setBackground(ripple(bg, 12));
        b.setStateListAnimator(null);
        b.setMinHeight(dp(48));
        b.setMinimumHeight(dp(48));
        b.setPadding(dp(14), dp(8), dp(14), dp(8));
        return b;
    }

    private void styleToggle(Button b, boolean active) {
        b.setBackground(ripple(active ? C_ACCENT : C_SOFT, 12));
        b.setTextColor(active ? Color.WHITE : C_TEXT);
    }
}
