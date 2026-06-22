package com.example.nasview;

import android.app.Activity;
import android.content.SharedPreferences;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.net.Uri;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.security.keystore.KeyGenParameterSpec;
import android.security.keystore.KeyProperties;
import android.text.Editable;
import android.text.InputType;
import android.text.TextWatcher;
import android.util.Base64;
import android.view.GestureDetector;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.GridLayout;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.ScrollView;
import android.widget.SeekBar;
import android.widget.TextView;
import android.widget.VideoView;

import com.hierynomus.msfscc.FileAttributes;
import com.hierynomus.msfscc.fileinformation.FileIdBothDirectoryInformation;
import com.hierynomus.msdtyp.AccessMask;
import com.hierynomus.mssmb2.SMB2CreateDisposition;
import com.hierynomus.mssmb2.SMB2CreateOptions;
import com.hierynomus.mssmb2.SMB2ShareAccess;
import com.hierynomus.smbj.SMBClient;
import com.hierynomus.smbj.auth.AuthenticationContext;
import com.hierynomus.smbj.connection.Connection;
import com.hierynomus.smbj.session.Session;
import com.hierynomus.smbj.share.DiskShare;
import com.hierynomus.smbj.share.File;

import java.io.ByteArrayOutputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Inet4Address;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.InetSocketAddress;
import java.net.SocketTimeoutException;
import java.nio.charset.StandardCharsets;
import java.security.KeyStore;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import javax.crypto.Cipher;
import javax.crypto.KeyGenerator;
import javax.crypto.SecretKey;
import javax.crypto.spec.GCMParameterSpec;

import jcifs.CIFSContext;
import jcifs.config.PropertyConfiguration;
import jcifs.context.BaseContext;
import jcifs.smb.NtlmPasswordAuthenticator;
import jcifs.smb.SmbFile;

public class MainActivity extends Activity {
    private static final String PREFS_NAME = "nas";
    private static final String DEFAULT_HOST_PREFIX = "192.168.";
    private static final String KEYSTORE_ALIAS = "nas_view_credentials";
    private static final String CREDENTIAL_SEPARATOR = "\u0000";
    private static final int SMB_PORT = 445;
    private static final int DISCOVERY_TIMEOUT_MS = 180;
    private static final int MAX_SCAN_DEPTH = 64;
    private static final int MAX_SCAN_ITEMS = 5000;
    private static final int SCREEN_CONNECTION = 0;
    private static final int SCREEN_SHARES = 1;
    private static final int SCREEN_MEDIA = 2;
    private static final int SCREEN_AUDIO_FOLDER = 3;
    private static final int SCREEN_VIEWER = 4;
    private static final int THUMBNAIL_SIZE = 160;
    private static final int SWIPE_MIN_DISTANCE_DP = 48;
    private static final int SWIPE_MAX_OFF_PATH_DP = 80;
    private static final int INITIAL_TILE_LIMIT = 60;
    private static final int LOAD_MORE_TILE_COUNT = 60;
    private static final long DIRECTORY_CACHE_TTL_MS = 15_000L;
    private static final int DIRECTORY_CACHE_MAX_ENTRIES = 20;
    private static final int MEDIA_IMAGE = 1;
    private static final int MEDIA_VIDEO = 2;
    private static final int MEDIA_AUDIO = 3;
    private static final int VIDEO_CONTROLS_AUTO_HIDE_MS = 3200;
    private static final int STREAM_BUFFER_SIZE = 256 * 1024;
    private static final int HISTORY_MAX_ENTRIES = 20;

    private final ExecutorService executor = Executors.newSingleThreadExecutor();
    private final ExecutorService thumbnailExecutor = Executors.newFixedThreadPool(2);
    private final ExecutorService discoveryExecutor = Executors.newSingleThreadExecutor();
    private final ExecutorService directoryExecutor = Executors.newFixedThreadPool(2);
    private LinearLayout root;
    private ProgressBar progress;
    private ScrollView contentScroll;
    private GridLayout currentGrid;
    private EditText hostInput;
    private EditText userInput;
    private EditText passwordInput;
    private LinearLayout discoveryResults;
    private TextView discoveryStatus;
    private Button discoveryButton;
    private int discoveryGeneration = 0;
    private final boolean scanAllFolders = true;
    private final boolean allSharesMode = true;
    private String currentPath = "";
    private String currentShareName = "";
    private String currentMediaPath = "";
    private List<RemoteItem> currentMediaItems = new ArrayList<>();
    private List<RemoteItem> currentRenderedItems = new ArrayList<>();
    private ArrayList<String> cachedShareNames = new ArrayList<>();
    private HashMap<String, Bitmap> visibleThumbnailCache = new HashMap<>();
    private final Set<ThumbnailLoad> activeThumbnailLoads = ConcurrentHashMap.newKeySet();
    private final LinkedHashMap<String, DirectoryCacheEntry> directoryCache =
            new LinkedHashMap<String, DirectoryCacheEntry>(16, 0.75f, true) {
                @Override
                protected boolean removeEldestEntry(Map.Entry<String, DirectoryCacheEntry> eldest) {
                    return size() > DIRECTORY_CACHE_MAX_ENTRIES;
                }
            };
    private int thumbnailGeneration = 0;
    private int viewerGeneration = 0;
    private int mediaDirectoryGeneration = 0;
    private int displayedTileCount = 0;
    private int contentHeaderCount = 1;
    private int screenState = SCREEN_CONNECTION;
    private String currentSearchQuery = "";
    private int currentSortMode = 0;
    private NasConfig config;
    private DirectoryLoad currentDirectoryLoad;
    private final SmbSessionPool smbSessionPool = new SmbSessionPool();
    private LocalStreamServer currentStreamServer;
    private VideoView currentPlayer;
    private RemoteItem currentPlayingItem;

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        if (!tryAutoConnect()) {
            showConnection(null);
        }
    }

    @Override
    protected void onDestroy() {
        stopCurrentStream();
        cancelCurrentDirectoryLoad();
        cancelThumbnailLoads();
        smbSessionPool.close();
        executor.shutdownNow();
        thumbnailExecutor.shutdownNow();
        discoveryExecutor.shutdownNow();
        directoryExecutor.shutdownNow();
        super.onDestroy();
    }

    @Override
    protected void onPause() {
        rememberCurrentFolderPosition();
        if (currentPlayer != null && currentPlayingItem != null) {
            try {
                savePlaybackPosition(currentPlayingItem, currentPlayer.getCurrentPosition());
            } catch (Exception ignored) {
                // Playback state will be saved again when the viewer closes.
            }
        }
        super.onPause();
    }

    @Override
    public void onBackPressed() {
        if (screenState == SCREEN_VIEWER) {
            if (currentShareName == null || currentShareName.isEmpty()) {
                showBrowser();
            } else {
                showMediaDirectory(currentShareName, currentMediaPath);
            }
            return;
        }
        if (screenState == SCREEN_AUDIO_FOLDER) {
            showCurrentMediaOverview();
            return;
        }
        if (screenState == SCREEN_MEDIA) {
            if (currentMediaPath != null && !currentMediaPath.isEmpty()) {
                showMediaDirectory(currentShareName, parentPath(currentMediaPath));
                return;
            }
            showBrowser();
            return;
        }
        if (screenState == SCREEN_SHARES) {
            showConnection(null);
            return;
        }
        super.onBackPressed();
    }

    private boolean tryAutoConnect() {
        SharedPreferences prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);
        String host = prefs.getString("host", "");
        if (host.isEmpty()) {
            return false;
        }

        Credentials credentials = loadCredentials();
        if (credentials == null) {
            return false;
        }

        config = new NasConfig(host, credentials.user, credentials.password);
        currentPath = "";
        String lastShare = prefs.getString("last_share", "");
        String lastPath = prefs.getString("last_path", "");
        if (lastShare.isEmpty()) {
            showBrowser();
        } else {
            showMediaDirectory(lastShare, lastPath);
        }
        return true;
    }

    private void showConnection(String message) {
        stopCurrentStream();
        cancelCurrentDirectoryLoad();
        leaveThumbnailScreen();
        screenState = SCREEN_CONNECTION;
        root = baseRoot();
        SharedPreferences prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);

        root.addView(title("NAS View"));
        if (message != null && !message.isEmpty()) {
            TextView notice = label(message);
            notice.setTextColor(0xff1d6f5f);
            root.addView(notice);
        }
        root.addView(label("NAS\u306e\u63a5\u7d9a\u60c5\u5831"));

        String savedHost = prefs.getString("host", DEFAULT_HOST_PREFIX);
        if (savedHost == null || savedHost.isEmpty()) {
            savedHost = DEFAULT_HOST_PREFIX;
        }
        hostInput = input("\u30db\u30b9\u30c8\u540d\u307e\u305f\u306fIP \u4f8b: 192.168.**.*", savedHost);

        Button discover = primaryButton("NAS\u3092\u81ea\u52d5\u691c\u7d22");
        discover.setOnClickListener(v -> startNasDiscovery());
        discoveryButton = discover;
        root.addView(discover);

        discoveryStatus = label("\u540c\u3058Wi-Fi\u307e\u305f\u306fLAN\u4e0a\u306eNAS\u3092\u691c\u7d22\u3067\u304d\u307e\u3059\u3002");
        root.addView(discoveryStatus);
        discoveryResults = new LinearLayout(this);
        discoveryResults.setOrientation(LinearLayout.VERTICAL);
        root.addView(discoveryResults);

        root.addView(label("\u307e\u305f\u306f\u63a5\u7d9a\u5148\u3092\u624b\u5165\u529b"));
        root.addView(hostInput);

        Credentials savedCredentials = loadCredentials();
        userInput = input("\u30e6\u30fc\u30b6\u30fc\u540d", savedCredentials == null ? "" : savedCredentials.user);
        passwordInput = input("\u30d1\u30b9\u30ef\u30fc\u30c9", savedCredentials == null ? "" : savedCredentials.password);
        passwordInput.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_VARIATION_PASSWORD);
        root.addView(userInput);
        root.addView(passwordInput);
        root.addView(label("\u8a8d\u8a3c\u60c5\u5831\u306f\u521d\u56de\u3060\u3051\u5165\u529b\u3057\u3001\u7aef\u672b\u5185\u306b\u6697\u53f7\u5316\u3057\u3066\u4fdd\u5b58\u3057\u307e\u3059\u3002"));

        Button connect = primaryButton("\u63a5\u7d9a");
        connect.setOnClickListener(v -> connectFromForm());
        root.addView(connect);

        if (!prefs.getString("host", "").isEmpty()) {
            Button clear = smallButton("\u4fdd\u5b58\u3057\u305f\u63a5\u7d9a\u60c5\u5831\u3092\u524a\u9664");
            clear.setOnClickListener(v -> {
                clearSavedConnection();
                showConnection("\u4fdd\u5b58\u3057\u305f\u63a5\u7d9a\u60c5\u5831\u3092\u524a\u9664\u3057\u307e\u3057\u305f\u3002");
            });
            root.addView(clear);
        }

        setContentView(wrap(root));
    }

    private void connectFromForm() {
        String host = hostInput.getText().toString().trim();
        String user = userInput.getText().toString().trim();
        String password = passwordInput.getText().toString();
        if (host.isEmpty() || user.isEmpty() || password.isEmpty()) {
            discoveryStatus.setText("\u63a5\u7d9a\u5148\u3001\u30e6\u30fc\u30b6\u30fc\u540d\u3001\u30d1\u30b9\u30ef\u30fc\u30c9\u3092\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
            return;
        }
        NasConfig candidate = new NasConfig(host, user, password);
        discoveryStatus.setText("\u63a5\u7d9a\u3092\u78ba\u8a8d\u4e2d\u3067\u3059\u2026");
        userInput.setEnabled(false);
        passwordInput.setEnabled(false);
        hostInput.setEnabled(false);
        executor.execute(() -> {
            try {
                ArrayList<String> shareNames = listShareNames(candidate);
                runOnUiThread(() -> {
                    config = candidate;
                    smbSessionPool.reset();
                    cachedShareNames = new ArrayList<>(shareNames);
                    clearDirectoryCache();
                    currentPath = "";
                    try {
                        saveConnectionSettings();
                        showBrowser();
                    } catch (Exception e) {
                        showConnection("\u63a5\u7d9a\u306f\u6210\u529f\u3057\u307e\u3057\u305f\u304c\u3001\u8a8d\u8a3c\u60c5\u5831\u3092\u5b89\u5168\u306b\u4fdd\u5b58\u3067\u304d\u307e\u305b\u3093\u3067\u3057\u305f\u3002");
                    }
                });
            } catch (Exception e) {
                runOnUiThread(() -> {
                    hostInput.setEnabled(true);
                    userInput.setEnabled(true);
                    passwordInput.setEnabled(true);
                    discoveryStatus.setText(errorMessageFor(e));
                });
            }
        });
    }

    private void saveConnectionSettings() throws Exception {
        saveCredentials(config.user, config.password);
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putString("host", config.host)
                .putString("path", currentPath)
                .remove("last_share")
                .remove("last_path")
                .apply();
    }

    private void clearSavedConnection() {
        discoveryGeneration++;
        cachedShareNames.clear();
        clearDirectoryCache();
        clearVisibleThumbnailCache();
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .edit()
                .clear()
                .apply();
        deleteCredentialKey();
        smbSessionPool.reset();
    }

    private void startNasDiscovery() {
        final int generation = ++discoveryGeneration;
        discoveryButton.setEnabled(false);
        discoveryResults.removeAllViews();
        discoveryStatus.setText("NAS\u3092\u691c\u7d22\u4e2d\u3067\u3059\u2026");

        discoveryExecutor.execute(() -> {
            String subnetPrefix = findLocalSubnetPrefix();
            if (subnetPrefix == null) {
                runOnUiThread(() -> finishDiscoveryWithMessage(
                        generation,
                        "\u63a5\u7d9a\u4e2d\u306eIPv4\u30cd\u30c3\u30c8\u30ef\u30fc\u30af\u3092\u78ba\u8a8d\u3067\u304d\u307e\u305b\u3093\u3067\u3057\u305f\u3002"
                ));
                return;
            }

            ArrayList<String> hosts = scanSmbHosts(subnetPrefix);
            runOnUiThread(() -> renderDiscoveredHosts(generation, hosts));
        });
    }

    private void finishDiscoveryWithMessage(int generation, String message) {
        if (screenState != SCREEN_CONNECTION || generation != discoveryGeneration) {
            return;
        }
        discoveryButton.setEnabled(true);
        discoveryStatus.setText(message);
    }

    private void renderDiscoveredHosts(int generation, List<String> hosts) {
        if (screenState != SCREEN_CONNECTION || generation != discoveryGeneration) {
            return;
        }
        discoveryButton.setEnabled(true);
        discoveryResults.removeAllViews();
        if (hosts.isEmpty()) {
            discoveryStatus.setText("NAS\u5019\u88dc\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093\u3067\u3057\u305f\u3002\u63a5\u7d9a\u5148\u3092\u624b\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
            return;
        }

        discoveryStatus.setText("\u898b\u3064\u304b\u3063\u305f\u63a5\u7d9a\u5019\u88dc\uff08\u30bf\u30c3\u30d7\u3067\u63a5\u7d9a\uff09");
        for (String host : hosts) {
            Button candidate = primaryButton("NAS  " + host);
            candidate.setOnClickListener(v -> selectDiscoveredHost(host));
            discoveryResults.addView(candidate);
        }
    }

    private void selectDiscoveredHost(String host) {
        hostInput.setText(host);
        if (userInput.getText().toString().trim().isEmpty()
                || passwordInput.getText().toString().isEmpty()) {
            discoveryStatus.setText("\u521d\u56de\u306e\u307f\u3001\u4e0b\u306e\u8a8d\u8a3c\u60c5\u5831\u3092\u5165\u529b\u3057\u3066\u300c\u63a5\u7d9a\u300d\u3092\u62bc\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
            userInput.requestFocus();
            return;
        }
        connectFromForm();
    }

    private String findLocalSubnetPrefix() {
        try {
            Enumeration<NetworkInterface> interfaces = NetworkInterface.getNetworkInterfaces();
            String fallback = null;
            while (interfaces.hasMoreElements()) {
                NetworkInterface network = interfaces.nextElement();
                if (!network.isUp() || network.isLoopback()) {
                    continue;
                }
                Enumeration<InetAddress> addresses = network.getInetAddresses();
                while (addresses.hasMoreElements()) {
                    InetAddress address = addresses.nextElement();
                    if (!(address instanceof Inet4Address) || address.isLoopbackAddress()) {
                        continue;
                    }
                    String hostAddress = address.getHostAddress();
                    int lastDot = hostAddress.lastIndexOf('.');
                    if (lastDot <= 0) {
                        continue;
                    }
                    String prefix = hostAddress.substring(0, lastDot + 1);
                    if (address.isSiteLocalAddress()) {
                        return prefix;
                    }
                    fallback = prefix;
                }
            }
            return fallback;
        } catch (Exception ignored) {
            return null;
        }
    }

    private ArrayList<String> scanSmbHosts(String subnetPrefix) {
        ExecutorService scanner = Executors.newFixedThreadPool(32);
        ArrayList<Future<String>> futures = new ArrayList<>();
        for (int suffix = 1; suffix <= 254; suffix++) {
            final String host = subnetPrefix + suffix;
            futures.add(scanner.submit((Callable<String>) () -> isSmbHost(host) ? host : null));
        }
        scanner.shutdown();

        ArrayList<String> hosts = new ArrayList<>();
        for (Future<String> future : futures) {
            try {
                String host = future.get();
                if (host != null) {
                    hosts.add(host);
                }
            } catch (Exception ignored) {
                // A single unreachable address should not stop discovery.
            }
        }
        return hosts;
    }

    private boolean isSmbHost(String host) {
        try (Socket socket = new Socket()) {
            socket.connect(new InetSocketAddress(host, SMB_PORT), DISCOVERY_TIMEOUT_MS);
            return true;
        } catch (Exception ignored) {
            return false;
        }
    }

    private void saveCredentials(String user, String password) throws Exception {
        Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
        cipher.init(Cipher.ENCRYPT_MODE, getOrCreateCredentialKey());
        byte[] plaintext = (user + CREDENTIAL_SEPARATOR + password).getBytes(StandardCharsets.UTF_8);
        byte[] encrypted = cipher.doFinal(plaintext);
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putString("credentials_iv", Base64.encodeToString(cipher.getIV(), Base64.NO_WRAP))
                .putString("credentials_data", Base64.encodeToString(encrypted, Base64.NO_WRAP))
                .apply();
    }

    private Credentials loadCredentials() {
        SharedPreferences prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);
        String ivText = prefs.getString("credentials_iv", "");
        String dataText = prefs.getString("credentials_data", "");
        if (ivText.isEmpty() || dataText.isEmpty()) {
            return null;
        }
        try {
            Cipher cipher = Cipher.getInstance("AES/GCM/NoPadding");
            cipher.init(
                    Cipher.DECRYPT_MODE,
                    getOrCreateCredentialKey(),
                    new GCMParameterSpec(128, Base64.decode(ivText, Base64.NO_WRAP))
            );
            String plaintext = new String(
                    cipher.doFinal(Base64.decode(dataText, Base64.NO_WRAP)),
                    StandardCharsets.UTF_8
            );
            int separator = plaintext.indexOf(CREDENTIAL_SEPARATOR);
            if (separator < 0) {
                return null;
            }
            return new Credentials(
                    plaintext.substring(0, separator),
                    plaintext.substring(separator + CREDENTIAL_SEPARATOR.length())
            );
        } catch (Exception ignored) {
            prefs.edit()
                    .remove("credentials_iv")
                    .remove("credentials_data")
                    .apply();
            return null;
        }
    }

    private SecretKey getOrCreateCredentialKey() throws Exception {
        KeyStore keyStore = KeyStore.getInstance("AndroidKeyStore");
        keyStore.load(null);
        java.security.Key existing = keyStore.getKey(KEYSTORE_ALIAS, null);
        if (existing instanceof SecretKey) {
            return (SecretKey) existing;
        }

        KeyGenerator generator = KeyGenerator.getInstance(
                KeyProperties.KEY_ALGORITHM_AES,
                "AndroidKeyStore"
        );
        generator.init(new KeyGenParameterSpec.Builder(
                KEYSTORE_ALIAS,
                KeyProperties.PURPOSE_ENCRYPT | KeyProperties.PURPOSE_DECRYPT
        ).setBlockModes(KeyProperties.BLOCK_MODE_GCM)
                .setEncryptionPaddings(KeyProperties.ENCRYPTION_PADDING_NONE)
                .build());
        return generator.generateKey();
    }

    private void deleteCredentialKey() {
        try {
            KeyStore keyStore = KeyStore.getInstance("AndroidKeyStore");
            keyStore.load(null);
            if (keyStore.containsAlias(KEYSTORE_ALIAS)) {
                keyStore.deleteEntry(KEYSTORE_ALIAS);
            }
        } catch (Exception ignored) {
            // Preferences are already cleared; a stale key contains no credential data.
        }
    }

    private void showBrowser() {
        stopCurrentStream();
        cancelCurrentDirectoryLoad();
        leaveThumbnailScreen();
        screenState = SCREEN_SHARES;
        currentShareName = "";
        mediaDirectoryGeneration++;
        currentGrid = null;
        currentRenderedItems = new ArrayList<>();
        displayedTileCount = 0;
        root = baseRoot();

        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(Gravity.CENTER_VERTICAL);

        Button settings = smallButton("\u63a5\u7d9a");
        settings.setOnClickListener(v -> showConnection(null));
        Button refresh = smallButton("\u66f4\u65b0");
        refresh.setOnClickListener(v -> {
            cachedShareNames.clear();
            showBrowser();
        });

        TextView title = new TextView(this);
        title.setText(config.host + " \u306e\u5171\u6709\u30d5\u30a9\u30eb\u30c0");
        title.setTextSize(16);
        title.setSingleLine(false);
        title.setPadding(dp(10), 0, 0, 0);
        bar.addView(settings);
        bar.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        bar.addView(refresh);
        root.addView(bar);

        progress = new ProgressBar(this);
        progress.setIndeterminate(true);
        root.addView(progress);
        setContentView(wrap(root));

        if (!cachedShareNames.isEmpty()) {
            renderShareNames(new ArrayList<>(cachedShareNames));
            return;
        }

        executor.execute(() -> {
            try {
                ArrayList<String> shareNames = listShareNames();
                cachedShareNames = new ArrayList<>(shareNames);
                runOnUiThread(() -> renderShareNames(shareNames));
            } catch (Exception e) {
                runOnUiThread(() -> renderError(e));
            }
        });
    }

    private void renderShareNames(List<String> shareNames) {
        root.removeView(progress);
        renderSavedShortcuts();
        if (shareNames.isEmpty()) {
            root.addView(label("\u8868\u793a\u3067\u304d\u308b\u5171\u6709\u30d5\u30a9\u30eb\u30c0\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093\u3002"));
            return;
        }
        GridLayout grid = new GridLayout(this);
        grid.setColumnCount(2);
        grid.setPadding(0, dp(8), 0, dp(20));
        root.addView(grid);

        int tileWidth = Math.max(dp(132), (getResources().getDisplayMetrics().widthPixels - dp(56)) / 2);
        for (String shareName : shareNames) {
            grid.addView(shareTile(shareName, tileWidth));
        }
    }

    private void showMediaList(String shareName) {
        screenState = SCREEN_MEDIA;
        currentShareName = shareName;
        currentMediaPath = "";
        currentPath = "";
        showMediaDirectory(shareName, "");
    }

    private void showMediaDirectory(String shareName, String path) {
        boolean sameFolder = shareName.equals(currentShareName) && path.equals(currentMediaPath);
        rememberCurrentFolderPosition();
        stopCurrentStream();
        cancelCurrentDirectoryLoad();
        leaveThumbnailScreen();
        screenState = SCREEN_MEDIA;
        currentShareName = shareName;
        currentMediaPath = path;
        if (!sameFolder) {
            currentSearchQuery = "";
        }
        addHistory(new RemoteItem(
                shareName,
                path.isEmpty() ? shareName : lastPathSegment(path),
                path,
                true
        ));
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putString("last_share", shareName)
                .putString("last_path", path)
                .apply();
        int loadGeneration = ++mediaDirectoryGeneration;
        currentMediaItems = new ArrayList<>();
        currentRenderedItems = new ArrayList<>();
        currentGrid = null;
        displayedTileCount = 0;

        root = baseRoot();
        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(Gravity.CENTER_VERTICAL);

        Button shares = smallButton("\u5171\u6709\u4e00\u89a7");
        shares.setOnClickListener(v -> showBrowser());
        Button favorite = smallButton(isFavorite(shareName, path) ? "\u2605" : "\u2606");
        favorite.setContentDescription("\u304a\u6c17\u306b\u5165\u308a");
        favorite.setOnClickListener(v -> {
            RemoteItem folder = new RemoteItem(
                    shareName,
                    path.isEmpty() ? shareName : lastPathSegment(path),
                    path,
                    true
            );
            toggleFavorite(folder);
            favorite.setText(isFavorite(shareName, path) ? "\u2605" : "\u2606");
        });
        Button refresh = smallButton("\u66f4\u65b0");
        refresh.setOnClickListener(v -> refreshCurrentDirectory());

        TextView title = new TextView(this);
        title.setText(path.isEmpty() ? shareName + " \u306e\u30e1\u30c7\u30a3\u30a2" : lastPathSegment(path));
        title.setTextSize(16);
        title.setSingleLine(false);
        title.setPadding(dp(10), 0, 0, 0);
        bar.addView(shares);
        bar.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        bar.addView(favorite);
        bar.addView(refresh);
        root.addView(bar);

        LinearLayout tools = new LinearLayout(this);
        tools.setOrientation(LinearLayout.HORIZONTAL);
        EditText search = input("\u3053\u306e\u30d5\u30a9\u30eb\u30c0\u3092\u691c\u7d22", currentSearchQuery);
        Button sort = smallButton(sortLabel());
        sort.setOnClickListener(v -> {
            currentSortMode = (currentSortMode + 1) % 3;
            sort.setText(sortLabel());
            applyMediaFilters();
        });
        search.addTextChangedListener(new TextWatcher() {
            @Override public void beforeTextChanged(CharSequence s, int start, int count, int after) {}
            @Override public void onTextChanged(CharSequence s, int start, int before, int count) {
                currentSearchQuery = s.toString();
                applyMediaFilters();
            }
            @Override public void afterTextChanged(Editable s) {}
        });
        tools.addView(search, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        tools.addView(sort);
        root.addView(tools);
        contentHeaderCount = 2;

        progress = new ProgressBar(this);
        progress.setIndeterminate(true);
        root.addView(progress);
        setContentView(wrap(root));

        List<RemoteItem> cachedItems = getCachedDirectory(shareName, path);
        if (cachedItems != null) {
            currentMediaItems = cachedItems;
            applyMediaFilters();
            return;
        }

        DirectoryLoad directoryLoad = new DirectoryLoad();
        currentDirectoryLoad = directoryLoad;
        directoryLoad.future = directoryExecutor.submit(() -> {
            try {
                List<RemoteItem> items = listDirectory(shareName, path, directoryLoad);
                if (directoryLoad.isCancelled()) {
                    return;
                }
                runOnUiThread(() -> {
                    if (directoryLoad.isCancelled()
                            || currentDirectoryLoad != directoryLoad
                            || !isCurrentMediaDirectory(loadGeneration, shareName, path)) {
                        return;
                    }
                    currentDirectoryLoad = null;
                    cacheDirectory(shareName, path, items);
                    currentMediaItems = items;
                    applyMediaFilters();
                });
            } catch (Exception e) {
                if (directoryLoad.isCancelled()) {
                    return;
                }
                runOnUiThread(() -> {
                    if (currentDirectoryLoad == directoryLoad
                            && isCurrentMediaDirectory(loadGeneration, shareName, path)) {
                        currentDirectoryLoad = null;
                        renderError(e);
                    }
                });
            } finally {
                directoryLoad.closeConnection();
            }
        });
    }

    private void cancelCurrentDirectoryLoad() {
        DirectoryLoad load = currentDirectoryLoad;
        currentDirectoryLoad = null;
        if (load != null) {
            load.cancel();
        }
    }

    private List<RemoteItem> getCachedDirectory(String shareName, String path) {
        String key = directoryCacheKey(shareName, path);
        synchronized (directoryCache) {
            DirectoryCacheEntry entry = directoryCache.get(key);
            if (entry == null) {
                return null;
            }
            if (System.currentTimeMillis() - entry.savedAt > DIRECTORY_CACHE_TTL_MS) {
                directoryCache.remove(key);
                return null;
            }
            return new ArrayList<>(entry.items);
        }
    }

    private void cacheDirectory(String shareName, String path, List<RemoteItem> items) {
        String key = directoryCacheKey(shareName, path);
        synchronized (directoryCache) {
            directoryCache.put(
                    key,
                    new DirectoryCacheEntry(System.currentTimeMillis(), new ArrayList<>(items))
            );
        }
    }

    private String directoryCacheKey(String shareName, String path) {
        String host = config == null ? "" : config.host;
        return host + "|" + shareName + "|" + path;
    }

    private void clearDirectoryCache() {
        synchronized (directoryCache) {
            directoryCache.clear();
        }
    }

    private boolean isCurrentMediaDirectory(int loadGeneration, String shareName, String path) {
        return screenState == SCREEN_MEDIA
                && mediaDirectoryGeneration == loadGeneration
                && currentShareName.equals(shareName)
                && currentMediaPath.equals(path);
    }
    private void renderItems(List<RemoteItem> items) {
        currentRenderedItems = items;
        displayedTileCount = 0;
        currentGrid = null;
        renderItemsWindow(INITIAL_TILE_LIMIT);
        restoreCurrentFolderPosition();
    }

    private void rememberCurrentFolderPosition() {
        if (screenState != SCREEN_MEDIA || contentScroll == null
                || currentShareName == null || currentShareName.isEmpty()) {
            return;
        }
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putInt("scroll_" + folderStateKey(currentShareName, currentMediaPath), contentScroll.getScrollY())
                .apply();
    }

    private void restoreCurrentFolderPosition() {
        if (contentScroll == null || currentShareName == null || currentShareName.isEmpty()) {
            return;
        }
        int position = getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .getInt("scroll_" + folderStateKey(currentShareName, currentMediaPath), 0);
        contentScroll.post(() -> contentScroll.scrollTo(0, position));
    }

    private String folderStateKey(String shareName, String path) {
        String host = config == null ? "" : config.host;
        String raw = host + "|" + shareName + "|" + path;
        return Base64.encodeToString(raw.getBytes(StandardCharsets.UTF_8), Base64.NO_WRAP | Base64.URL_SAFE);
    }

    private void renderItemsWindow(int limit) {
        if (progress != null && progress.getParent() == root) {
            root.removeView(progress);
        }
        if (currentRenderedItems.isEmpty()) {
            while (root.getChildCount() > contentHeaderCount) {
                root.removeViewAt(contentHeaderCount);
            }
            root.addView(label("\u5bfe\u5fdc\u3057\u3066\u3044\u308b\u30e1\u30c7\u30a3\u30a2\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093\u3002"));
            return;
        }

        if (currentGrid == null) {
            while (root.getChildCount() > contentHeaderCount) {
                root.removeViewAt(contentHeaderCount);
            }
            currentGrid = new GridLayout(this);
            currentGrid.setColumnCount(2);
            currentGrid.setPadding(0, dp(8), 0, dp(20));
            root.addView(currentGrid);
        }

        int tileWidth = Math.max(dp(132), (getResources().getDisplayMetrics().widthPixels - dp(56)) / 2);
        int end = Math.min(displayedTileCount + limit, currentRenderedItems.size());
        for (int i = displayedTileCount; i < end; i++) {
            currentGrid.addView(thumbnailTile(currentRenderedItems.get(i), tileWidth));
        }
        displayedTileCount = end;
    }

    private void maybeLoadMoreTiles() {
        if (currentGrid == null || displayedTileCount >= currentRenderedItems.size()) {
            return;
        }
        renderItemsWindow(LOAD_MORE_TILE_COUNT);
    }

    private void applyMediaFilters() {
        thumbnailGeneration++;
        cancelThumbnailLoads();
        ArrayList<RemoteItem> filtered = new ArrayList<>();
        String query = currentSearchQuery.trim().toLowerCase(Locale.ROOT);
        for (RemoteItem item : groupAudioByFolder(currentMediaItems)) {
            if (query.isEmpty()
                    || item.name.toLowerCase(Locale.ROOT).contains(query)
                    || item.path.toLowerCase(Locale.ROOT).contains(query)) {
                filtered.add(item);
            }
        }
        Comparator<RemoteItem> comparator;
        if (currentSortMode == 1) {
            comparator = (a, b) -> b.name.compareToIgnoreCase(a.name);
        } else if (currentSortMode == 2) {
            comparator = Comparator
                    .comparingInt((RemoteItem item) -> item.directory ? 0 : mediaSortOrder(item.name))
                    .thenComparing(item -> item.name.toLowerCase(Locale.ROOT));
        } else {
            comparator = (a, b) -> a.name.compareToIgnoreCase(b.name);
        }
        Collections.sort(filtered, (a, b) -> {
            if (a.directory != b.directory) {
                return a.directory ? -1 : 1;
            }
            return comparator.compare(a, b);
        });
        renderItems(filtered);
    }

    private int mediaSortOrder(String name) {
        if (isImage(name)) return 1;
        if (isZip(name)) return 2;
        if (isVideo(name)) return 3;
        if (isAudio(name)) return 4;
        return 5;
    }

    private String sortLabel() {
        if (currentSortMode == 1) return "\u540d\u524d \u2193";
        if (currentSortMode == 2) return "\u7a2e\u985e\u9806";
        return "\u540d\u524d \u2191";
    }

    private void refreshCurrentDirectory() {
        if (currentShareName == null || currentShareName.isEmpty()) {
            cachedShareNames.clear();
            showBrowser();
            return;
        }
        synchronized (directoryCache) {
            directoryCache.remove(directoryCacheKey(currentShareName, currentMediaPath));
        }
        showMediaDirectory(currentShareName, currentMediaPath);
    }

    private void renderSavedShortcuts() {
        List<RemoteItem> favorites = favoriteItems();
        List<RemoteItem> history = historyItems();
        if (!favorites.isEmpty()) {
            root.addView(label("\u304a\u6c17\u306b\u5165\u308a"));
            renderShortcutButtons(favorites, 8);
        }
        if (!history.isEmpty()) {
            root.addView(label("\u6700\u8fd1\u958b\u3044\u305f\u9805\u76ee"));
            renderShortcutButtons(history, 6);
        }
    }

    private void renderShortcutButtons(List<RemoteItem> items, int limit) {
        LinearLayout shortcuts = new LinearLayout(this);
        shortcuts.setOrientation(LinearLayout.VERTICAL);
        for (int i = 0; i < Math.min(limit, items.size()); i++) {
            RemoteItem item = items.get(i);
            Button button = smallButton((item.directory ? "\u30d5\u30a9\u30eb\u30c0  " : "") + item.name);
            button.setGravity(Gravity.START | Gravity.CENTER_VERTICAL);
            button.setOnClickListener(v -> openItem(item));
            shortcuts.addView(button);
        }
        root.addView(shortcuts);
    }

    private boolean isFavorite(String share, String path) {
        String prefix = shortcutIdentity(share, path);
        for (String encoded : favoriteRecords()) {
            if (encoded.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private void toggleFavorite(RemoteItem item) {
        HashSet<String> records = favoriteRecords();
        String prefix = shortcutIdentity(item.share, item.path);
        String existing = null;
        for (String record : records) {
            if (record.startsWith(prefix)) {
                existing = record;
                break;
            }
        }
        if (existing == null) {
            records.add(encodeShortcut(item));
        } else {
            records.remove(existing);
        }
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putStringSet("favorites", records)
                .apply();
    }

    private HashSet<String> favoriteRecords() {
        return new HashSet<>(getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .getStringSet("favorites", Collections.emptySet()));
    }

    private List<RemoteItem> favoriteItems() {
        ArrayList<RemoteItem> items = new ArrayList<>();
        for (String record : favoriteRecords()) {
            RemoteItem item = decodeShortcut(record);
            if (item != null) items.add(item);
        }
        Collections.sort(items, Comparator.comparing(item -> item.name.toLowerCase(Locale.ROOT)));
        return items;
    }

    private void addHistory(RemoteItem item) {
        String encoded = encodeShortcut(item);
        ArrayList<String> records = historyRecords();
        records.removeIf(record -> record.startsWith(shortcutIdentity(item.share, item.path)));
        records.add(0, encoded);
        if (records.size() > HISTORY_MAX_ENTRIES) {
            records.subList(HISTORY_MAX_ENTRIES, records.size()).clear();
        }
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putString("history", String.join(",", records))
                .apply();
    }

    private ArrayList<String> historyRecords() {
        String stored = getSharedPreferences(PREFS_NAME, MODE_PRIVATE).getString("history", "");
        ArrayList<String> records = new ArrayList<>();
        if (stored != null && !stored.isEmpty()) {
            Collections.addAll(records, stored.split(","));
        }
        return records;
    }

    private List<RemoteItem> historyItems() {
        ArrayList<RemoteItem> items = new ArrayList<>();
        for (String record : historyRecords()) {
            RemoteItem item = decodeShortcut(record);
            if (item != null) items.add(item);
        }
        return items;
    }

    private String shortcutIdentity(String share, String path) {
        String host = config == null ? "" : config.host;
        String raw = host + "\u0000" + share + "\u0000" + path + "\u0000";
        return Base64.encodeToString(raw.getBytes(StandardCharsets.UTF_8), Base64.NO_WRAP | Base64.URL_SAFE)
                .replace("=", "");
    }

    private String encodeShortcut(RemoteItem item) {
        String identity = shortcutIdentity(item.share, item.path);
        String details = item.name + "\u0000" + item.directory;
        return identity + "." + Base64.encodeToString(
                details.getBytes(StandardCharsets.UTF_8),
                Base64.NO_WRAP | Base64.URL_SAFE
        );
    }

    private RemoteItem decodeShortcut(String record) {
        try {
            int dot = record.indexOf('.');
            if (dot < 0) return null;
            String identityPart = record.substring(0, dot);
            int padding = (4 - identityPart.length() % 4) % 4;
            StringBuilder padded = new StringBuilder(identityPart);
            for (int i = 0; i < padding; i++) padded.append('=');
            String identity = new String(
                    Base64.decode(padded.toString(), Base64.NO_WRAP | Base64.URL_SAFE),
                    StandardCharsets.UTF_8
            );
            String[] fields = identity.split(CREDENTIAL_SEPARATOR, -1);
            if (fields.length < 4 || config == null || !config.host.equals(fields[0])) return null;
            String details = new String(
                    Base64.decode(record.substring(dot + 1), Base64.NO_WRAP | Base64.URL_SAFE),
                    StandardCharsets.UTF_8
            );
            String[] detailFields = details.split(CREDENTIAL_SEPARATOR, -1);
            if (detailFields.length < 2) return null;
            return new RemoteItem(fields[1], detailFields[0], fields[2], Boolean.parseBoolean(detailFields[1]));
        } catch (Exception ignored) {
            return null;
        }
    }

    private void renderError(Exception e) {
        if (progress != null && progress.getParent() == root) {
            root.removeView(progress);
        }
        root.addView(label(errorMessageFor(e)));
        TextView detail = label(e.getMessage() == null ? e.getClass().getSimpleName() : e.getMessage());
        detail.setTextColor(0xff9b1c1c);
        root.addView(detail);
        Button retry = smallButton("\u518d\u8a66\u884c");
        retry.setOnClickListener(v -> {
            if (screenState == SCREEN_MEDIA) {
                refreshCurrentDirectory();
            } else {
                cachedShareNames.clear();
                showBrowser();
            }
        });
        root.addView(retry);
        Button edit = smallButton("\u63a5\u7d9a\u60c5\u5831\u3092\u78ba\u8a8d");
        edit.setOnClickListener(v -> showConnection("\u63a5\u7d9a\u3067\u304d\u307e\u305b\u3093\u3067\u3057\u305f\u3002\u63a5\u7d9a\u60c5\u5831\u3092\u78ba\u8a8d\u3057\u3066\u304f\u3060\u3055\u3044\u3002"));
        root.addView(edit);
    }

    private String errorMessageFor(Exception e) {
        String text = ((e.getMessage() == null ? "" : e.getMessage()) + " "
                + e.getClass().getSimpleName()).toLowerCase(Locale.ROOT);
        if (text.contains("auth") || text.contains("logon") || text.contains("password")
                || text.contains("access_denied") || text.contains("status_logon_failure")) {
            return "\u8a8d\u8a3c\u306b\u5931\u6557\u3057\u307e\u3057\u305f\u3002\u30e6\u30fc\u30b6\u30fc\u540d\u3068\u30d1\u30b9\u30ef\u30fc\u30c9\u3092\u78ba\u8a8d\u3057\u3066\u304f\u3060\u3055\u3044\u3002";
        }
        if (text.contains("denied") || text.contains("permission")) {
            return "\u3053\u306e\u30d5\u30a9\u30eb\u30c0\u3092\u958b\u304f\u6a29\u9650\u304c\u3042\u308a\u307e\u305b\u3093\u3002";
        }
        if (text.contains("timeout") || e instanceof SocketTimeoutException) {
            return "NAS\u304b\u3089\u306e\u5fdc\u7b54\u304c\u306a\u3044\u305f\u3081\u30bf\u30a4\u30e0\u30a2\u30a6\u30c8\u3057\u307e\u3057\u305f\u3002";
        }
        if (text.contains("unreachable") || text.contains("refused")
                || text.contains("unknownhost") || text.contains("connect")) {
            return "NAS\u306b\u63a5\u7d9a\u3067\u304d\u307e\u305b\u3093\u3002Wi-Fi\u3068NAS\u306e\u96fb\u6e90\u3092\u78ba\u8a8d\u3057\u3066\u304f\u3060\u3055\u3044\u3002";
        }
        return "\u63a5\u7d9a\u307e\u305f\u306f\u8aad\u307f\u8fbc\u307f\u306b\u5931\u6557\u3057\u307e\u3057\u305f\u3002";
    }

    private void openItem(RemoteItem item) {
        addHistory(item);
        if (item.directory) {
            if (item.audioGroup) {
                renderAudioFolder(item);
            } else {
                showMediaDirectory(item.share, item.path);
            }
            return;
        }
        if (isImage(item.name)) {
            showImage(item);
        } else if (isZip(item.name)) {
            showZip(item);
        } else if (isPlayable(item.name)) {
            showPlayer(item);
        }
    }

    private void saveCurrentPath() {
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .edit()
                .putString("path", currentPath)
                .apply();
    }

    private void renderAudioFolder(RemoteItem folder) {
        rememberCurrentFolderPosition();
        leaveThumbnailScreen();
        screenState = SCREEN_AUDIO_FOLDER;
        root = baseRoot();
        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(Gravity.CENTER_VERTICAL);

        Button back = smallButton("\u30e1\u30c7\u30a3\u30a2");
        back.setOnClickListener(v -> showCurrentMediaOverview());

        TextView title = new TextView(this);
        title.setText(folder.name);
        title.setTextSize(16);
        title.setSingleLine(false);
        title.setPadding(dp(10), 0, 0, 0);
        bar.addView(back);
        bar.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        root.addView(bar);
        contentHeaderCount = 1;
        setContentView(wrap(root));

        ArrayList<RemoteItem> audioItems = new ArrayList<>();
        for (RemoteItem item : currentMediaItems) {
            if (isAudio(item.name)
                    && item.share.equals(folder.share)
                    && parentPath(item.path).equals(folder.path)) {
                audioItems.add(item);
            }
        }
        renderItems(audioItems);
    }

    private void showCurrentMediaOverview() {
        leaveThumbnailScreen();
        screenState = SCREEN_MEDIA;
        root = baseRoot();
        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(Gravity.CENTER_VERTICAL);

        Button shares = smallButton("\u5171\u6709\u4e00\u89a7");
        shares.setOnClickListener(v -> showBrowser());

        TextView title = new TextView(this);
        title.setText(currentMediaPath.isEmpty() ? currentShareName + " \u306e\u30e1\u30c7\u30a3\u30a2" : lastPathSegment(currentMediaPath));
        title.setTextSize(16);
        title.setSingleLine(false);
        title.setPadding(dp(10), 0, 0, 0);
        bar.addView(shares);
        bar.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        root.addView(bar);
        contentHeaderCount = 1;
        setContentView(wrap(root));
        renderItems(groupAudioByFolder(currentMediaItems));
    }

    private void showImage(RemoteItem item) {
        rememberCurrentFolderPosition();
        stopCurrentStream();
        leaveThumbnailScreen();
        screenState = SCREEN_VIEWER;
        viewerGeneration++;
        FrameLayout frame = viewerFrame(item.name);
        ProgressBar loading = centeredProgress(frame);
        setContentView(frame);

        executor.execute(() -> {
            try {
                byte[] bytes = readRemoteFile(item.share, item.path);
                Bitmap bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.length);
                runOnUiThread(() -> {
                    frame.removeView(loading);
                    ImageView image = new ImageView(this);
                    image.setImageBitmap(bitmap);
                    image.setAdjustViewBounds(true);
                    image.setScaleType(ImageView.ScaleType.FIT_CENTER);
                    addImageSwipeNavigation(image, item);
                    frame.addView(image, fillBelowToolbar());
                });
            } catch (Exception e) {
                runOnUiThread(() -> showMessageInFrame(frame, loading, e));
            }
        });
    }

    private void addImageSwipeNavigation(View view, RemoteItem item) {
        final float[] down = new float[2];
        view.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                down[0] = event.getX();
                down[1] = event.getY();
                return true;
            }
            if (event.getAction() == MotionEvent.ACTION_UP) {
                float dx = event.getX() - down[0];
                float dy = event.getY() - down[1];
                if (Math.abs(dx) > dp(SWIPE_MIN_DISTANCE_DP)
                        && Math.abs(dy) < dp(SWIPE_MAX_OFF_PATH_DP)) {
                    RemoteItem next = adjacentImage(item, dx < 0 ? 1 : -1);
                    if (next != null) {
                        showImage(next);
                    }
                    return true;
                }
            }
            return true;
        });
    }

    private void showPlayer(RemoteItem item) {
        rememberCurrentFolderPosition();
        stopCurrentStream();
        leaveThumbnailScreen();
        screenState = SCREEN_VIEWER;
        int playerGeneration = ++viewerGeneration;
        FrameLayout frame = viewerFrame(item.name);
        ProgressBar loading = centeredProgress(frame);
        setContentView(frame);

        try {
            currentStreamServer = new LocalStreamServer(item);
            currentStreamServer.start();
            frame.removeView(loading);
            FrameLayout playerArea = new FrameLayout(this);
            playerArea.setBackgroundColor(0xff000000);

            VideoView player = new ResponsiveVideoView(this);
            currentPlayer = player;
            currentPlayingItem = item;
            player.setVideoURI(Uri.parse(currentStreamServer.getUrl()));
                    playerArea.addView(player, new FrameLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            Gravity.CENTER
                    ));

                    FrameLayout controls = new FrameLayout(this);
                    controls.setBackgroundColor(0x55000000);

                    LinearLayout centerControls = new LinearLayout(this);
                    centerControls.setGravity(Gravity.CENTER);
                    centerControls.setOrientation(LinearLayout.HORIZONTAL);

                    LinearLayout bottomControls = new LinearLayout(this);
                    bottomControls.setOrientation(LinearLayout.VERTICAL);
                    bottomControls.setPadding(dp(12), dp(8), dp(12), dp(12));
                    bottomControls.setBackgroundColor(0x99000000);

                    LinearLayout transportRow = new LinearLayout(this);
                    transportRow.setGravity(Gravity.CENTER_VERTICAL);
                    transportRow.setOrientation(LinearLayout.HORIZONTAL);

                    TextView time = videoTimeLabel("0:00 / 0:00");
                    SeekBar seekBar = new SeekBar(this);
                    boolean videoItem = isVideo(item.name);
                    Button prevVideo = overlayIconButton("\u23ee", videoItem ? "\u524d\u306e\u52d5\u753b" : "\u524d\u306e\u97f3\u58f0", 42);
                    Button playPause = overlayIconButton("\u23f8", "\u4e00\u6642\u505c\u6b62", 70);
                    Button nextVideo = overlayIconButton("\u23ed", videoItem ? "\u6b21\u306e\u52d5\u753b" : "\u6b21\u306e\u97f3\u58f0", 42);

                    RemoteItem previous = videoItem ? adjacentVideo(item, -1) : adjacentAudio(item, -1);
                    RemoteItem next = videoItem ? adjacentVideo(item, 1) : adjacentAudio(item, 1);
                    prevVideo.setEnabled(previous != null);
                    nextVideo.setEnabled(next != null);
                    prevVideo.setOnClickListener(v -> {
                        if (previous != null) {
                            showPlayer(previous);
                        }
                    });
                    nextVideo.setOnClickListener(v -> {
                        if (next != null) {
                            showPlayer(next);
                        }
                    });
                    playPause.setOnClickListener(v -> {
                        if (player.isPlaying()) {
                            player.pause();
                            playPause.setText("\u25b6");
                            playPause.setContentDescription("\u518d\u751f");
                            playPause.setTooltipText("\u518d\u751f");
                        } else {
                            player.start();
                            playPause.setText("\u23f8");
                            playPause.setContentDescription("\u4e00\u6642\u505c\u6b62");
                            playPause.setTooltipText("\u4e00\u6642\u505c\u6b62");
                        }
                    });

                    centerControls.addView(playPause);
                    controls.addView(centerControls, new FrameLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.WRAP_CONTENT,
                            Gravity.CENTER
                    ));

                    transportRow.addView(prevVideo);
                    transportRow.addView(time, new LinearLayout.LayoutParams(
                            0,
                            ViewGroup.LayoutParams.WRAP_CONTENT,
                            1
                    ));
                    transportRow.addView(nextVideo);
                    bottomControls.addView(transportRow);
                    bottomControls.addView(seekBar, new LinearLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.WRAP_CONTENT
                    ));
                    controls.addView(bottomControls, new FrameLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.WRAP_CONTENT,
                            Gravity.BOTTOM
                    ));
                    playerArea.addView(controls, new FrameLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT,
                            ViewGroup.LayoutParams.MATCH_PARENT
                    ));

                    frame.addView(playerArea, fillBelowToolbar());
                    setupVideoControlsVisibility(playerArea, controls, player, playerGeneration);
                    setupVideoSeekControls(player, seekBar, time, playerGeneration, controls, item);
                    player.start();
        } catch (Exception e) {
            showMessageInFrame(frame, loading, e);
        }
    }

    private void setupVideoControlsVisibility(View touchArea, View controls, VideoView player, int playerGeneration) {
        Handler handler = new Handler(Looper.getMainLooper());
        Runnable[] hide = new Runnable[1];
        hide[0] = () -> {
            if (screenState != SCREEN_VIEWER || viewerGeneration != playerGeneration) {
                return;
            }
            if (player.isPlaying()) {
                controls.setVisibility(View.INVISIBLE);
            } else {
                handler.postDelayed(hide[0], VIDEO_CONTROLS_AUTO_HIDE_MS);
            }
        };
        Runnable show = () -> {
            controls.setVisibility(View.VISIBLE);
            handler.removeCallbacks(hide[0]);
            handler.postDelayed(hide[0], VIDEO_CONTROLS_AUTO_HIDE_MS);
        };
        GestureDetector detector = new GestureDetector(this, new GestureDetector.SimpleOnGestureListener() {
            @Override
            public boolean onDown(MotionEvent event) {
                return true;
            }

            @Override
            public boolean onSingleTapConfirmed(MotionEvent event) {
                if (controls.getVisibility() == View.VISIBLE) {
                    controls.setVisibility(View.INVISIBLE);
                } else {
                    show.run();
                }
                return true;
            }

            @Override
            public boolean onDoubleTap(MotionEvent event) {
                if (event.getX() < touchArea.getWidth() / 2f) {
                    player.seekTo(Math.max(0, player.getCurrentPosition() - 10000));
                } else {
                    int duration = player.getDuration();
                    int target = player.getCurrentPosition() + 10000;
                    player.seekTo(duration > 0 ? Math.min(duration, target) : target);
                }
                controls.setVisibility(View.INVISIBLE);
                return true;
            }
        });
        View.OnTouchListener listener = (v, event) -> detector.onTouchEvent(event);
        touchArea.setOnTouchListener(listener);
        controls.setOnTouchListener(listener);
        show.run();
    }

    private void setupVideoSeekControls(
            VideoView player,
            SeekBar seekBar,
            TextView time,
            int playerGeneration,
            View controls,
            RemoteItem item
    ) {
        Handler handler = new Handler(Looper.getMainLooper());
        final boolean[] userSeeking = {false};
        Runnable[] updater = new Runnable[1];
        updater[0] = () -> {
            int duration = Math.max(0, player.getDuration());
            int position = Math.max(0, player.getCurrentPosition());
            if (!userSeeking[0]) {
                seekBar.setMax(duration);
                seekBar.setProgress(Math.min(position, duration));
            }
            time.setText(formatTime(position) + " / " + formatTime(duration));
            if (screenState == SCREEN_VIEWER && viewerGeneration == playerGeneration) {
                handler.postDelayed(updater[0], 500);
            }
        };
        seekBar.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
            @Override
            public void onProgressChanged(SeekBar bar, int progress, boolean fromUser) {
                if (fromUser) {
                    time.setText(formatTime(progress) + " / " + formatTime(Math.max(0, player.getDuration())));
                }
            }

            @Override
            public void onStartTrackingTouch(SeekBar bar) {
                controls.setVisibility(View.VISIBLE);
                userSeeking[0] = true;
            }

            @Override
            public void onStopTrackingTouch(SeekBar bar) {
                player.seekTo(bar.getProgress());
                controls.setVisibility(View.VISIBLE);
                userSeeking[0] = false;
            }
        });
        player.setOnPreparedListener(mp -> {
            if (player instanceof ResponsiveVideoView) {
                ((ResponsiveVideoView) player).setVideoSize(mp.getVideoWidth(), mp.getVideoHeight());
            }
            seekBar.setMax(player.getDuration());
            int savedPosition = getSavedPlaybackPosition(item);
            if (savedPosition > 0 && savedPosition < player.getDuration() - 3000) {
                player.seekTo(savedPosition);
            }
            updater[0].run();
        });
    }

    private RemoteItem adjacentImage(RemoteItem current, int direction) {
        return adjacentMedia(current, direction, MEDIA_IMAGE);
    }

    private RemoteItem adjacentVideo(RemoteItem current, int direction) {
        return adjacentMedia(current, direction, MEDIA_VIDEO);
    }

    private RemoteItem adjacentAudio(RemoteItem current, int direction) {
        return adjacentMedia(current, direction, MEDIA_AUDIO);
    }

    private RemoteItem adjacentMedia(RemoteItem current, int direction, int mediaType) {
        ArrayList<RemoteItem> media = new ArrayList<>();
        for (RemoteItem item : currentMediaItems) {
            if (!item.directory && matchesMediaType(item.name, mediaType)) {
                media.add(item);
            }
        }
        sortItems(media);
        for (int i = 0; i < media.size(); i++) {
            RemoteItem item = media.get(i);
            if (item.share.equals(current.share) && item.path.equals(current.path)) {
                int nextIndex = i + direction;
                if (nextIndex >= 0 && nextIndex < media.size()) {
                    return media.get(nextIndex);
                }
                return null;
            }
        }
        return null;
    }

    private boolean matchesMediaType(String name, int mediaType) {
        if (mediaType == MEDIA_IMAGE) return isImage(name);
        if (mediaType == MEDIA_VIDEO) return isVideo(name);
        if (mediaType == MEDIA_AUDIO) return isAudio(name);
        return false;
    }

    private String formatTime(int millis) {
        int totalSeconds = Math.max(0, millis / 1000);
        int seconds = totalSeconds % 60;
        int minutes = (totalSeconds / 60) % 60;
        int hours = totalSeconds / 3600;
        if (hours > 0) {
            return String.format(Locale.US, "%d:%02d:%02d", hours, minutes, seconds);
        }
        return String.format(Locale.US, "%d:%02d", minutes, seconds);
    }

    private void stopCurrentStream() {
        if (currentPlayer != null && currentPlayingItem != null) {
            try {
                savePlaybackPosition(currentPlayingItem, currentPlayer.getCurrentPosition());
                currentPlayer.stopPlayback();
            } catch (Exception ignored) {
                // The player may already have released its media resources.
            }
        }
        currentPlayer = null;
        currentPlayingItem = null;
        if (currentStreamServer != null) {
            currentStreamServer.stop();
            currentStreamServer = null;
        }
    }

    private void savePlaybackPosition(RemoteItem item, int position) {
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putInt("playback_" + mediaStateKey(item), Math.max(0, position))
                .apply();
    }

    private int getSavedPlaybackPosition(RemoteItem item) {
        return getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .getInt("playback_" + mediaStateKey(item), 0);
    }

    private String mediaStateKey(RemoteItem item) {
        String host = config == null ? "" : config.host;
        String raw = host + "|" + item.share + "|" + item.path;
        return Base64.encodeToString(raw.getBytes(StandardCharsets.UTF_8), Base64.NO_WRAP | Base64.URL_SAFE);
    }

    private void showZip(RemoteItem item) {
        rememberCurrentFolderPosition();
        stopCurrentStream();
        leaveThumbnailScreen();
        screenState = SCREEN_VIEWER;
        viewerGeneration++;
        FrameLayout frame = viewerFrame(item.name);
        ProgressBar loading = centeredProgress(frame);
        setContentView(frame);

        executor.execute(() -> {
            try {
                ArrayList<String> pages = listZipImageEntries(item.share, item.path);
                if (pages.isEmpty()) {
                    throw new IllegalStateException("zip\u5185\u306b\u753b\u50cf\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093\u3002");
                }
                int savedPage = getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                        .getInt("zip_" + mediaStateKey(item), 0);
                int initialPage = Math.max(0, Math.min(savedPage, pages.size() - 1));
                runOnUiThread(() -> renderZipPage(frame, loading, item, pages, initialPage));
            } catch (Exception e) {
                runOnUiThread(() -> showMessageInFrame(frame, loading, e));
            }
        });
    }

    private void renderZipPage(FrameLayout frame, View oldView, RemoteItem item, ArrayList<String> pages, int index) {
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putInt("zip_" + mediaStateKey(item), index)
                .apply();
        if (oldView != null) {
            frame.removeView(oldView);
        }
        ProgressBar loading = centeredProgress(frame);
        executor.execute(() -> {
            try {
                byte[] bytes = readZipEntry(item.share, item.path, pages.get(index));
                Bitmap bitmap = BitmapFactory.decodeByteArray(bytes, 0, bytes.length);
                runOnUiThread(() -> {
                    frame.removeView(loading);
                    LinearLayout page = new LinearLayout(this);
                    page.setOrientation(LinearLayout.VERTICAL);

                    ImageView image = new ImageView(this);
                    image.setImageBitmap(bitmap);
                    image.setAdjustViewBounds(true);
                    image.setScaleType(ImageView.ScaleType.FIT_CENTER);
                    page.addView(image, new LinearLayout.LayoutParams(
                            ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
                    addZipSwipeNavigation(page, frame, item, pages, index);

                    LinearLayout controls = new LinearLayout(this);
                    controls.setGravity(Gravity.CENTER);
                    Button prev = smallButton("\u524d");
                    Button next = smallButton("\u6b21");
                    TextView count = label((index + 1) + " / " + pages.size());
                    prev.setEnabled(index > 0);
                    next.setEnabled(index < pages.size() - 1);
                    prev.setOnClickListener(v -> renderZipPage(frame, page, item, pages, index - 1));
                    next.setOnClickListener(v -> renderZipPage(frame, page, item, pages, index + 1));
                    controls.addView(prev);
                    controls.addView(count);
                    controls.addView(next);
                    page.addView(controls);

                    frame.addView(page, fillBelowToolbar());
                });
            } catch (Exception e) {
                runOnUiThread(() -> showMessageInFrame(frame, loading, e));
            }
        });
    }

    private void addZipSwipeNavigation(View view, FrameLayout frame, RemoteItem item, ArrayList<String> pages, int index) {
        final float[] down = new float[2];
        view.setOnTouchListener((v, event) -> {
            if (event.getAction() == MotionEvent.ACTION_DOWN) {
                down[0] = event.getX();
                down[1] = event.getY();
                return true;
            }
            if (event.getAction() == MotionEvent.ACTION_UP) {
                float dx = event.getX() - down[0];
                float dy = event.getY() - down[1];
                if (Math.abs(dx) > dp(SWIPE_MIN_DISTANCE_DP)
                        && Math.abs(dy) < dp(SWIPE_MAX_OFF_PATH_DP)) {
                    if (dx < 0 && index < pages.size() - 1) {
                        renderZipPage(frame, view, item, pages, index + 1);
                    } else if (dx > 0 && index > 0) {
                        renderZipPage(frame, view, item, pages, index - 1);
                    }
                    return true;
                }
            }
            return true;
        });
    }

    private FrameLayout viewerFrame(String name) {
        FrameLayout frame = new FrameLayout(this);
        LinearLayout toolbar = new LinearLayout(this);
        toolbar.setOrientation(LinearLayout.HORIZONTAL);
        toolbar.setGravity(Gravity.CENTER_VERTICAL);
        toolbar.setPadding(dp(10), dp(8), dp(10), dp(8));
        toolbar.setBackgroundColor(0xfff2f5f3);
        Button back = smallButton("\u623b\u308b");
        back.setOnClickListener(v -> {
            if (currentShareName == null || currentShareName.isEmpty()) {
                showBrowser();
            } else {
                showMediaDirectory(currentShareName, currentMediaPath);
            }
        });
        TextView title = label(name);
        title.setSingleLine(true);
        toolbar.addView(back);
        toolbar.addView(title, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        FrameLayout.LayoutParams toolbarParams = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(56),
                Gravity.TOP
        );
        toolbarParams.topMargin = dp(24);
        frame.addView(toolbar, toolbarParams);
        return frame;
    }

    private FrameLayout.LayoutParams fillBelowToolbar() {
        FrameLayout.LayoutParams params = new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT
        );
        params.topMargin = dp(80);
        return params;
    }

    private ProgressBar centeredProgress(FrameLayout frame) {
        ProgressBar progressBar = new ProgressBar(this);
        progressBar.setIndeterminate(true);
        frame.addView(progressBar, new FrameLayout.LayoutParams(dp(52), dp(52), Gravity.CENTER));
        return progressBar;
    }

    private void showMessageInFrame(FrameLayout frame, View loading, Exception e) {
        if (loading != null) {
            frame.removeView(loading);
        }
        TextView message = label(e.getMessage() == null ? e.toString() : e.getMessage());
        message.setGravity(Gravity.CENTER);
        frame.addView(message, fillBelowToolbar());
    }

    private View shareTile(String shareName, int tileWidth) {
        LinearLayout tile = new LinearLayout(this);
        tile.setOrientation(LinearLayout.VERTICAL);
        tile.setPadding(dp(8), dp(8), dp(8), dp(8));
        tile.setBackgroundColor(0xfff4f7f6);
        tile.setOnClickListener(v -> showMediaList(shareName));

        GridLayout.LayoutParams params = new GridLayout.LayoutParams();
        params.width = tileWidth;
        params.height = ViewGroup.LayoutParams.WRAP_CONTENT;
        params.setMargins(dp(4), dp(6), dp(4), dp(8));
        tile.setLayoutParams(params);

        TextView preview = label("\u5171\u6709");
        preview.setGravity(Gravity.CENTER);
        preview.setTextSize(20);
        preview.setBackgroundColor(0xffe5ebe8);
        tile.addView(preview, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(96)
        ));

        TextView name = label(shareName);
        name.setTextSize(14);
        name.setMaxLines(2);
        tile.addView(name);
        return tile;
    }

    private View thumbnailTile(RemoteItem item, int tileWidth) {
        LinearLayout tile = new LinearLayout(this);
        tile.setOrientation(LinearLayout.VERTICAL);
        tile.setPadding(dp(8), dp(8), dp(8), dp(8));
        tile.setBackgroundColor(0xfff4f7f6);
        tile.setOnClickListener(v -> openItem(item));

        GridLayout.LayoutParams params = new GridLayout.LayoutParams();
        params.width = tileWidth;
        params.height = ViewGroup.LayoutParams.WRAP_CONTENT;
        params.setMargins(dp(4), dp(6), dp(4), dp(8));
        tile.setLayoutParams(params);

        FrameLayout preview = new FrameLayout(this);
        preview.setBackgroundColor(0xffe5ebe8);
        tile.addView(preview, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                dp(120)
        ));

        ImageView image = new ImageView(this);
        image.setScaleType(ImageView.ScaleType.CENTER_CROP);
        preview.addView(image, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT
        ));

        TextView badge = label(mediaPrefix(item.name));
        badge.setGravity(Gravity.CENTER);
        badge.setTextSize(18);
        preview.addView(badge, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT
        ));

        TextView name = label(item.audioGroup ? item.displayName(false) : item.name);
        name.setTextSize(13);
        name.setMaxLines(2);
        LinearLayout nameRow = new LinearLayout(this);
        nameRow.setOrientation(LinearLayout.HORIZONTAL);
        nameRow.setGravity(Gravity.CENTER_VERTICAL);
        nameRow.addView(name, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        Button favorite = smallButton(isFavorite(item.share, item.path) ? "\u2605" : "\u2606");
        favorite.setMinWidth(dp(42));
        favorite.setOnClickListener(v -> {
            toggleFavorite(item);
            favorite.setText(isFavorite(item.share, item.path) ? "\u2605" : "\u2606");
        });
        nameRow.addView(favorite);
        tile.addView(nameRow);

        TextView path = label(item.audioGroup ? item.share + "/" + item.path : item.share + "/" + parentPath(item.path));
        path.setTextSize(11);
        path.setTextColor(0xff60736d);
        path.setMaxLines(1);
        tile.addView(path);

        if (item.audioGroup) {
            badge.setText("\u97f3\u58f0\u30d5\u30a9\u30eb\u30c0");
        } else if (isImage(item.name) || isZip(item.name)) {
            int generation = thumbnailGeneration;
            ThumbnailLoad thumbnailLoad = new ThumbnailLoad();
            activeThumbnailLoads.add(thumbnailLoad);
            thumbnailLoad.future = thumbnailExecutor.submit(() -> {
                try {
                    Bitmap bitmap = loadVisibleThumbnailBitmap(item, thumbnailLoad);
                    if (bitmap != null) {
                        runOnUiThread(() -> {
                            if (thumbnailLoad.isCancelled()
                                    || generation != thumbnailGeneration) {
                                return;
                            }
                            image.setImageBitmap(bitmap);
                            badge.setVisibility(View.GONE);
                        });
                    }
                } catch (Exception ignored) {
                    // Leave the media-type tile when thumbnail generation fails.
                } finally {
                    thumbnailLoad.closeConnection();
                    activeThumbnailLoads.remove(thumbnailLoad);
                }
            });
        }

        return tile;
    }

    private List<RemoteItem> groupAudioByFolder(List<RemoteItem> items) {
        ArrayList<RemoteItem> grouped = new ArrayList<>();
        LinkedHashMap<String, AudioFolderInfo> audioFolders = new LinkedHashMap<>();

        for (RemoteItem item : items) {
            if (isAudio(item.name)) {
                String folderPath = parentPath(item.path);
                String key = item.share + "/" + folderPath;
                AudioFolderInfo info = audioFolders.get(key);
                if (info == null) {
                    info = new AudioFolderInfo(item.share, folderPath);
                    audioFolders.put(key, info);
                }
                info.count++;
            } else {
                grouped.add(item);
            }
        }

        for (AudioFolderInfo info : audioFolders.values()) {
            String name = info.path.isEmpty() ? info.share : lastPathSegment(info.path);
            grouped.add(RemoteItem.audioFolder(info.share, name, info.path, info.count));
        }
        sortItems(grouped);
        return grouped;
    }

    private Bitmap loadVisibleThumbnailBitmap(RemoteItem item, ThumbnailLoad thumbnailLoad) throws Exception {
        String key = thumbnailKey(item);
        Bitmap cached;
        synchronized (visibleThumbnailCache) {
            cached = visibleThumbnailCache.get(key);
        }
        if (cached != null) {
            return cached;
        }

        Bitmap generated = loadThumbnailBitmap(item, thumbnailLoad);
        if (generated != null
                && !thumbnailLoad.isCancelled()
                && screenState == SCREEN_MEDIA) {
            synchronized (visibleThumbnailCache) {
                visibleThumbnailCache.put(key, generated);
            }
        }
        return generated;
    }

    private Bitmap loadThumbnailBitmap(RemoteItem item, ThumbnailLoad thumbnailLoad) throws Exception {
        return withThumbnailShare(item.share, thumbnailLoad, share -> {
            byte[] bytes;
            if (isZip(item.name)) {
                ArrayList<String> pages = listZipImageEntries(share, item.path, thumbnailLoad);
                if (pages.isEmpty() || thumbnailLoad.isCancelled()) {
                    return null;
                }
                bytes = readZipEntry(share, item.path, pages.get(0), thumbnailLoad);
            } else {
                bytes = readRemoteFile(share, item.path, thumbnailLoad);
            }
            if (thumbnailLoad.isCancelled()) {
                return null;
            }
            return decodeSampledBitmap(bytes, dp(THUMBNAIL_SIZE), dp(THUMBNAIL_SIZE));
        });
    }

    private String thumbnailKey(RemoteItem item) {
        return config.host + "|" + item.share + "|" + item.path;
    }

    private void clearVisibleThumbnailCache() {
        synchronized (visibleThumbnailCache) {
            visibleThumbnailCache.clear();
        }
    }

    private void leaveThumbnailScreen() {
        thumbnailGeneration++;
        cancelThumbnailLoads();
        clearVisibleThumbnailCache();
    }

    private void cancelThumbnailLoads() {
        ArrayList<ThumbnailLoad> loads = new ArrayList<>(activeThumbnailLoads);
        activeThumbnailLoads.clear();
        for (ThumbnailLoad load : loads) {
            load.cancel();
        }
    }

    private Bitmap decodeSampledBitmap(byte[] bytes, int reqWidth, int reqHeight) {
        BitmapFactory.Options options = new BitmapFactory.Options();
        options.inJustDecodeBounds = true;
        BitmapFactory.decodeByteArray(bytes, 0, bytes.length, options);
        options.inSampleSize = calculateInSampleSize(options, reqWidth, reqHeight);
        options.inJustDecodeBounds = false;
        return BitmapFactory.decodeByteArray(bytes, 0, bytes.length, options);
    }

    private int calculateInSampleSize(BitmapFactory.Options options, int reqWidth, int reqHeight) {
        int height = options.outHeight;
        int width = options.outWidth;
        int inSampleSize = 1;
        while ((height / inSampleSize) > reqHeight || (width / inSampleSize) > reqWidth) {
            inSampleSize *= 2;
        }
        return Math.max(1, inSampleSize);
    }

    private List<RemoteItem> listDirectory(
            String shareName,
            String path,
            DirectoryLoad directoryLoad
    ) throws Exception {
        if (config == null || config.host.isEmpty() || shareName == null || shareName.isEmpty()) {
            throw new IllegalStateException("\u30db\u30b9\u30c8\u540d\u307e\u305f\u306fIP\u3092\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
        }
        NasConfig loadConfig = config;
        try (SMBClient client = new SMBClient();
             Connection connection = client.connect(loadConfig.host)) {
            directoryLoad.attachConnection(connection);
            AuthenticationContext auth = new AuthenticationContext(
                    loadConfig.user,
                    loadConfig.password.toCharArray(),
                    null
            );
            Session session = connection.authenticate(auth);
            try (DiskShare share = (DiskShare) session.connectShare(shareName)) {
                if (directoryLoad.isCancelled()) {
                    return Collections.emptyList();
                }
            ArrayList<RemoteItem> items = new ArrayList<>();
            for (FileIdBothDirectoryInformation info : share.list(path)) {
                if (directoryLoad.isCancelled()) {
                    return Collections.emptyList();
                }
                String name = info.getFileName();
                if (".".equals(name) || "..".equals(name)) {
                    continue;
                }
                boolean directory = isDirectory(info);
                String childPath = joinPath(path, name);
                if (directory || isSupported(name)) {
                    items.add(new RemoteItem(shareName, name, childPath, directory));
                }
            }
            sortItems(items);
            return items;
            } finally {
                directoryLoad.detachConnection(connection);
            }
        }
    }

    private List<RemoteItem> listAllSharesMedia() throws Exception {
        ArrayList<RemoteItem> items = new ArrayList<>();
        for (String shareName : listShareNames()) {
            if (items.size() >= MAX_SCAN_ITEMS) {
                break;
            }
            try {
                items.addAll(listAllMedia(shareName, ""));
                if (items.size() > MAX_SCAN_ITEMS) {
                    items.subList(MAX_SCAN_ITEMS, items.size()).clear();
                }
            } catch (Exception ignored) {
                // Some NAS shares may be visible but not readable by this account.
            }
        }
        sortItems(items);
        return items;
    }

    private List<RemoteItem> listAllMedia(String shareName, String path) throws Exception {
        return withShare(shareName, share -> {
            ArrayList<RemoteItem> items = new ArrayList<>();
            scanMediaTree(shareName, share, path, items, 0);
            sortItems(items);
            return items;
        });
    }

    private <T> T withThumbnailShare(
            String shareName,
            ThumbnailLoad thumbnailLoad,
            ShareAction<T> action
    ) throws Exception {
        if (config == null || config.host.isEmpty() || shareName == null || shareName.isEmpty()) {
            throw new IllegalStateException("\u30db\u30b9\u30c8\u540d\u307e\u305f\u306fIP\u3092\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
        }
        NasConfig loadConfig = config;
        try (SMBClient client = new SMBClient();
             Connection connection = client.connect(loadConfig.host)) {
            thumbnailLoad.attachConnection(connection);
            AuthenticationContext auth = new AuthenticationContext(
                    loadConfig.user,
                    loadConfig.password.toCharArray(),
                    null
            );
            Session session = connection.authenticate(auth);
            try (DiskShare share = (DiskShare) session.connectShare(shareName)) {
                if (thumbnailLoad.isCancelled()) {
                    return null;
                }
                return action.run(share);
            } finally {
                thumbnailLoad.detachConnection(connection);
            }
        }
    }

    private byte[] readRemoteFile(
            DiskShare share,
            String path,
            ThumbnailLoad thumbnailLoad
    ) throws Exception {
        try (File file = openReadFile(share, path);
             InputStream input = file.getInputStream();
             ByteArrayOutputStream output = new ByteArrayOutputStream()) {
            copy(input, output, thumbnailLoad);
            return output.toByteArray();
        }
    }

    private ArrayList<String> listZipImageEntries(
            DiskShare share,
            String path,
            ThumbnailLoad thumbnailLoad
    ) throws Exception {
        ArrayList<String> names = new ArrayList<>();
        try (File file = openReadFile(share, path);
             ZipInputStream zip = new ZipInputStream(file.getInputStream())) {
            ZipEntry entry;
            while (!thumbnailLoad.isCancelled() && (entry = zip.getNextEntry()) != null) {
                if (!entry.isDirectory() && isImage(entry.getName())) {
                    names.add(entry.getName());
                }
            }
        }
        Collections.sort(names, Comparator.naturalOrder());
        return names;
    }

    private byte[] readZipEntry(
            DiskShare share,
            String path,
            String entryName,
            ThumbnailLoad thumbnailLoad
    ) throws Exception {
        try (File file = openReadFile(share, path);
             ZipInputStream zip = new ZipInputStream(file.getInputStream());
             ByteArrayOutputStream output = new ByteArrayOutputStream()) {
            ZipEntry entry;
            while (!thumbnailLoad.isCancelled() && (entry = zip.getNextEntry()) != null) {
                if (entryName.equals(entry.getName())) {
                    copy(zip, output, thumbnailLoad);
                    return output.toByteArray();
                }
            }
        }
        if (thumbnailLoad.isCancelled()) {
            return new byte[0];
        }
        throw new IllegalStateException("\u30da\u30fc\u30b8\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093: " + entryName);
    }

    private void scanMediaTree(String shareName, DiskShare share, String path, ArrayList<RemoteItem> items, int depth) {
        if (depth > MAX_SCAN_DEPTH || items.size() >= MAX_SCAN_ITEMS) {
            return;
        }
        for (FileIdBothDirectoryInformation info : share.list(path)) {
            String name = info.getFileName();
            if (".".equals(name) || "..".equals(name)) {
                continue;
            }
            String childPath = joinPath(path, name);
            if (isDirectory(info)) {
                scanMediaTree(shareName, share, childPath, items, depth + 1);
            } else if (isSupported(name)) {
                items.add(new RemoteItem(shareName, name, childPath, false));
                if (items.size() >= MAX_SCAN_ITEMS) {
                    return;
                }
            }
        }
    }

    private byte[] readRemoteFile(String shareName, String path) throws Exception {
        return withShare(shareName, share -> {
            try (File file = openReadFile(share, path);
                 InputStream input = file.getInputStream();
                 ByteArrayOutputStream output = new ByteArrayOutputStream()) {
                copy(input, output);
                return output.toByteArray();
            }
        });
    }

    private ArrayList<String> listZipImageEntries(String shareName, String path) throws Exception {
        return withShare(shareName, share -> {
            ArrayList<String> names = new ArrayList<>();
            try (File file = openReadFile(share, path);
                 ZipInputStream zip = new ZipInputStream(file.getInputStream())) {
                ZipEntry entry;
                while ((entry = zip.getNextEntry()) != null) {
                    if (!entry.isDirectory() && isImage(entry.getName())) {
                        names.add(entry.getName());
                    }
                }
            }
            Collections.sort(names, Comparator.naturalOrder());
            return names;
        });
    }

    private byte[] readZipEntry(String shareName, String path, String entryName) throws Exception {
        return withShare(shareName, share -> {
            try (File file = openReadFile(share, path);
                 ZipInputStream zip = new ZipInputStream(file.getInputStream());
                 ByteArrayOutputStream output = new ByteArrayOutputStream()) {
                ZipEntry entry;
                while ((entry = zip.getNextEntry()) != null) {
                    if (entryName.equals(entry.getName())) {
                        copy(zip, output);
                        return output.toByteArray();
                    }
                }
            }
            throw new IllegalStateException("\u30da\u30fc\u30b8\u304c\u898b\u3064\u304b\u308a\u307e\u305b\u3093: " + entryName);
        });
    }

    private File openReadFile(DiskShare share, String path) {
        return share.openFile(
                path,
                EnumSet.of(AccessMask.GENERIC_READ),
                EnumSet.noneOf(FileAttributes.class),
                SMB2ShareAccess.ALL,
                SMB2CreateDisposition.FILE_OPEN,
                EnumSet.of(SMB2CreateOptions.FILE_NON_DIRECTORY_FILE)
        );
    }

    private class LocalStreamServer {
        private final RemoteItem item;
        private final ExecutorService clients = Executors.newFixedThreadPool(2);
        private final AtomicBoolean running = new AtomicBoolean(false);
        private ServerSocket serverSocket;
        private Thread acceptThread;

        LocalStreamServer(RemoteItem item) {
            this.item = item;
        }

        void start() throws Exception {
            serverSocket = new ServerSocket();
            serverSocket.setReuseAddress(true);
            serverSocket.bind(new InetSocketAddress(InetAddress.getByName("127.0.0.1"), 0));
            running.set(true);
            acceptThread = new Thread(() -> {
                while (running.get()) {
                    try {
                        Socket socket = serverSocket.accept();
                        clients.execute(() -> handleClient(socket));
                    } catch (Exception e) {
                        if (running.get()) {
                            // VideoView retries the URL when a transient request fails.
                        }
                    }
                }
            }, "nas-stream-accept");
            acceptThread.start();
        }

        String getUrl() {
            return "http://127.0.0.1:" + serverSocket.getLocalPort() + "/media";
        }

        void stop() {
            running.set(false);
            if (serverSocket != null) {
                try {
                    serverSocket.close();
                } catch (Exception ignored) {
                    // Closing wakes the accept loop.
                }
            }
            clients.shutdownNow();
            if (acceptThread != null) {
                acceptThread.interrupt();
            }
        }

        private void handleClient(Socket socket) {
            try (Socket client = socket) {
                client.setSoTimeout(15_000);
                BufferedReader reader = new BufferedReader(new InputStreamReader(
                        client.getInputStream(),
                        StandardCharsets.ISO_8859_1
                ));
                String requestLine = reader.readLine();
                if (requestLine == null) {
                    return;
                }
                boolean headOnly = requestLine.startsWith("HEAD ");
                String range = null;
                String line;
                while ((line = reader.readLine()) != null && !line.isEmpty()) {
                    int separator = line.indexOf(':');
                    if (separator > 0 && "range".equalsIgnoreCase(line.substring(0, separator).trim())) {
                        range = line.substring(separator + 1).trim();
                    }
                }
                final String requestedRange = range;
                withShare(item.share, share -> {
                    streamResponse(
                            share,
                            item.path,
                            mimeType(item.name),
                            requestedRange,
                            headOnly,
                            client.getOutputStream()
                    );
                    return null;
                });
            } catch (Exception ignored) {
                // VideoView can abandon a range request when the user seeks again.
            }
        }

        private void streamResponse(
                DiskShare share,
                String path,
                String mime,
                String range,
                boolean headOnly,
                OutputStream output
        ) throws Exception {
            long total = share.getFileInformation(path)
                    .getStandardInformation()
                    .getEndOfFile();
            long start = 0;
            long end = Math.max(0, total - 1);
            boolean partial = range != null && range.startsWith("bytes=");
            if (partial) {
                String value = range.substring(6);
                String[] parts = value.split("-", 2);
                if (!parts[0].isEmpty()) {
                    start = Math.max(0, Long.parseLong(parts[0]));
                }
                if (parts.length > 1 && !parts[1].isEmpty()) {
                    end = Math.min(end, Long.parseLong(parts[1]));
                }
            }
            if (start >= total || end < start) {
                output.write(("HTTP/1.1 416 Range Not Satisfiable\r\n"
                        + "Content-Range: bytes */" + total + "\r\n"
                        + "Connection: close\r\n\r\n").getBytes(StandardCharsets.ISO_8859_1));
                return;
            }

            long length = end - start + 1;
            StringBuilder headers = new StringBuilder();
            headers.append(partial ? "HTTP/1.1 206 Partial Content\r\n" : "HTTP/1.1 200 OK\r\n");
            headers.append("Accept-Ranges: bytes\r\n");
            headers.append("Content-Type: ").append(mime).append("\r\n");
            headers.append("Content-Length: ").append(length).append("\r\n");
            if (partial) {
                headers.append("Content-Range: bytes ").append(start).append("-").append(end)
                        .append("/").append(total).append("\r\n");
            }
            headers.append("Connection: close\r\n\r\n");
            output.write(headers.toString().getBytes(StandardCharsets.ISO_8859_1));
            if (headOnly) {
                return;
            }

            try (File file = openReadFile(share, path)) {
                byte[] buffer = new byte[STREAM_BUFFER_SIZE];
                long offset = start;
                long remaining = length;
                while (running.get() && remaining > 0) {
                    int requested = (int) Math.min(buffer.length, remaining);
                    int read = file.read(buffer, offset, 0, requested);
                    if (read <= 0) {
                        break;
                    }
                    output.write(buffer, 0, read);
                    offset += read;
                    remaining -= read;
                }
                output.flush();
            }
        }
    }

    private static String mimeType(String name) {
        String lower = lower(name);
        if (lower.endsWith(".mp4") || lower.endsWith(".m4v")) return "video/mp4";
        if (lower.endsWith(".mkv")) return "video/x-matroska";
        if (lower.endsWith(".webm")) return "video/webm";
        if (lower.endsWith(".3gp")) return "video/3gpp";
        if (lower.endsWith(".avi")) return "video/x-msvideo";
        if (lower.endsWith(".mp3")) return "audio/mpeg";
        if (lower.endsWith(".m4a")) return "audio/mp4";
        if (lower.endsWith(".aac")) return "audio/aac";
        if (lower.endsWith(".wav")) return "audio/wav";
        if (lower.endsWith(".flac")) return "audio/flac";
        if (lower.endsWith(".ogg")) return "audio/ogg";
        return "application/octet-stream";
    }

    private ArrayList<String> listShareNames() throws Exception {
        return listShareNames(config);
    }

    private ArrayList<String> listShareNames(NasConfig targetConfig) throws Exception {
        if (targetConfig == null || targetConfig.host.isEmpty()) {
            throw new IllegalStateException("\u30db\u30b9\u30c8\u540d\u307e\u305f\u306fIP\u3092\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
        }

        Properties properties = new Properties();
        properties.setProperty("jcifs.smb.client.enableSMB2", "true");
        properties.setProperty("jcifs.smb.client.disableSMB1", "false");
        CIFSContext base = new BaseContext(new PropertyConfiguration(properties));
        NtlmPasswordAuthenticator auth = new NtlmPasswordAuthenticator(
                null,
                targetConfig.user,
                targetConfig.password
        );
        CIFSContext context = base.withCredentials(auth);
        ArrayList<String> names = new ArrayList<>();
        try (SmbFile root = new SmbFile("smb://" + targetConfig.host + "/", context)) {
            for (SmbFile file : root.listFiles()) {
                String name = file.getName();
                if (!name.endsWith("/")) {
                    continue;
                }
                name = name.substring(0, name.length() - 1);
                if (!name.endsWith("$") && !"IPC$".equalsIgnoreCase(name) && !"print$".equalsIgnoreCase(name)) {
                    names.add(name);
                }
            }
        }
        Collections.sort(names, String::compareToIgnoreCase);
        return names;
    }

    private <T> T withShare(String shareName, ShareAction<T> action) throws Exception {
        if (config == null || config.host.isEmpty() || shareName == null || shareName.isEmpty()) {
            throw new IllegalStateException("\u30db\u30b9\u30c8\u540d\u307e\u305f\u306fIP\u3092\u5165\u529b\u3057\u3066\u304f\u3060\u3055\u3044\u3002");
        }
        return smbSessionPool.withShare(config, shareName, action);
    }

    private LinearLayout baseRoot() {
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(dp(16), dp(34), dp(16), dp(18));
        layout.setBackgroundColor(0xffffffff);
        return layout;
    }

    private ScrollView wrap(View content) {
        contentScroll = new ScrollView(this);
        contentScroll.addView(content);
        contentScroll.setOnScrollChangeListener((v, scrollX, scrollY, oldScrollX, oldScrollY) -> {
            View child = contentScroll.getChildAt(0);
            if (child == null || scrollY <= oldScrollY) {
                return;
            }
            int remaining = child.getBottom() - (contentScroll.getHeight() + scrollY);
            if (remaining < dp(360)) {
                maybeLoadMoreTiles();
            }
        });
        return contentScroll;
    }

    private TextView title(String text) {
        TextView view = label(text);
        view.setTextSize(28);
        view.setTextColor(0xff10231f);
        view.setPadding(0, dp(12), 0, dp(18));
        return view;
    }

    private TextView label(String text) {
        TextView view = new TextView(this);
        view.setText(text);
        view.setTextSize(15);
        view.setTextColor(0xff263a35);
        view.setPadding(dp(4), dp(8), dp(4), dp(8));
        return view;
    }

    private EditText input(String hint, String value) {
        EditText editText = new EditText(this);
        editText.setHint(hint);
        editText.setText(value);
        editText.setSingleLine(true);
        editText.setTextSize(16);
        editText.setPadding(dp(10), dp(8), dp(10), dp(8));
        return editText;
    }

    private Button primaryButton(String text) {
        Button button = new Button(this);
        button.setText(text);
        button.setAllCaps(false);
        button.setTextSize(17);
        button.setPadding(dp(10), dp(10), dp(10), dp(10));
        return button;
    }

    private Button smallButton(String text) {
        Button button = new Button(this);
        button.setText(text);
        button.setAllCaps(false);
        button.setTextSize(14);
        button.setMinHeight(dp(42));
        return button;
    }

    private Button iconButton(String icon, String description) {
        Button button = smallButton(icon);
        button.setTextSize(20);
        button.setContentDescription(description);
        button.setTooltipText(description);
        button.setMinWidth(dp(56));
        button.setMinHeight(dp(44));
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
        );
        params.setMargins(dp(2), dp(2), dp(2), dp(2));
        button.setLayoutParams(params);
        return button;
    }

    private Button overlayIconButton(String icon, String description, int sizeDp) {
        Button button = iconButton(icon, description);
        button.setTextSize(sizeDp >= 64 ? 28 : 20);
        button.setTextColor(0xffffffff);
        button.setBackgroundColor(0x66000000);
        LinearLayout.LayoutParams params = new LinearLayout.LayoutParams(dp(sizeDp), dp(sizeDp));
        params.setMargins(dp(6), dp(4), dp(6), dp(4));
        button.setLayoutParams(params);
        return button;
    }

    private TextView videoTimeLabel(String text) {
        TextView view = label(text);
        view.setTextColor(0xffffffff);
        view.setTextSize(13);
        view.setGravity(Gravity.CENTER);
        view.setPadding(dp(8), dp(2), dp(8), dp(2));
        return view;
    }

    private Button rowButton(RemoteItem item) {
        String label = item.directory
                ? "\u30d5\u30a9\u30eb\u30c0  " + item.name
                : mediaPrefix(item.name) + "  " + item.displayName(true);
        Button button = primaryButton(label);
        button.setGravity(Gravity.CENTER_VERTICAL | Gravity.START);
        return button;
    }

    private String mediaPrefix(String name) {
        if (isImage(name)) return "\u753b\u50cf";
        if (isZip(name)) return "\u30de\u30f3\u30ac";
        if (isAudio(name)) return "\u97f3\u58f0";
        if (isVideo(name)) return "\u6620\u50cf";
        return "\u30d5\u30a1\u30a4\u30eb";
    }

    private static String lastPathSegment(String path) {
        if (path == null || path.isEmpty()) {
            return "";
        }
        int index = path.lastIndexOf('/');
        return index >= 0 ? path.substring(index + 1) : path;
    }

    private static void sortItems(ArrayList<RemoteItem> items) {
        Collections.sort(items, (a, b) -> {
            if (a.directory != b.directory) {
                return a.directory ? -1 : 1;
            }
            int shareCompare = a.share.compareToIgnoreCase(b.share);
            if (shareCompare != 0) {
                return shareCompare;
            }
            return a.path.compareToIgnoreCase(b.path);
        });
    }

    private static boolean isDirectory(FileIdBothDirectoryInformation info) {
        return (info.getFileAttributes() & FileAttributes.FILE_ATTRIBUTE_DIRECTORY.getValue()) != 0;
    }

    private static void copy(InputStream input, OutputStream output) throws Exception {
        byte[] buffer = new byte[64 * 1024];
        int read;
        while ((read = input.read(buffer)) != -1) {
            output.write(buffer, 0, read);
        }
    }

    private static void copy(
            InputStream input,
            OutputStream output,
            ThumbnailLoad thumbnailLoad
    ) throws Exception {
        byte[] buffer = new byte[64 * 1024];
        int read;
        while (!thumbnailLoad.isCancelled() && (read = input.read(buffer)) != -1) {
            output.write(buffer, 0, read);
        }
    }

    private static String normalizePath(String value) {
        String path = value.trim().replace('\\', '/');
        while (path.startsWith("/")) {
            path = path.substring(1);
        }
        while (path.endsWith("/")) {
            path = path.substring(0, path.length() - 1);
        }
        return path;
    }

    private static String joinPath(String parent, String child) {
        return parent == null || parent.isEmpty() ? child : parent + "/" + child;
    }

    private static String parentPath(String path) {
        if (path == null || path.isEmpty() || !path.contains("/")) {
            return "";
        }
        return path.substring(0, path.lastIndexOf('/'));
    }

    private static boolean isSupported(String name) {
        return isImage(name) || isVideo(name) || isAudio(name) || isZip(name);
    }

    private static boolean isPlayable(String name) {
        return isVideo(name) || isAudio(name);
    }

    private static boolean isImage(String name) {
        String lower = lower(name);
        return lower.endsWith(".jpg") || lower.endsWith(".jpeg") || lower.endsWith(".png")
                || lower.endsWith(".webp") || lower.endsWith(".gif") || lower.endsWith(".bmp");
    }

    private static boolean isVideo(String name) {
        String lower = lower(name);
        return lower.endsWith(".mp4") || lower.endsWith(".m4v") || lower.endsWith(".mkv")
                || lower.endsWith(".webm") || lower.endsWith(".3gp") || lower.endsWith(".avi");
    }

    private static boolean isAudio(String name) {
        String lower = lower(name);
        return lower.endsWith(".mp3") || lower.endsWith(".m4a") || lower.endsWith(".aac")
                || lower.endsWith(".wav") || lower.endsWith(".flac") || lower.endsWith(".ogg");
    }

    private static boolean isZip(String name) {
        return lower(name).endsWith(".zip");
    }

    private static String lower(String name) {
        return name.toLowerCase(Locale.ROOT);
    }

    private int dp(int value) {
        return (int) (value * getResources().getDisplayMetrics().density + 0.5f);
    }

    private interface ShareAction<T> {
        T run(DiskShare share) throws Exception;
    }

    private static class SmbSessionPool {
        private SMBClient client;
        private Connection connection;
        private Session session;
        private String identity = "";

        <T> T withShare(NasConfig config, String shareName, ShareAction<T> action) throws Exception {
            DiskShare share;
            try {
                share = (DiskShare) getSession(config).connectShare(shareName);
            } catch (Exception connectionFailure) {
                reset();
                share = (DiskShare) getSession(config).connectShare(shareName);
            }
            try (DiskShare activeShare = share) {
                return action.run(activeShare);
            }
        }

        private synchronized Session getSession(NasConfig config) throws Exception {
            String requestedIdentity = config.host + "\u0000" + config.user + "\u0000" + config.password;
            if (session != null && requestedIdentity.equals(identity)) {
                return session;
            }
            reset();
            client = new SMBClient();
            connection = client.connect(config.host);
            AuthenticationContext auth = new AuthenticationContext(
                    config.user,
                    config.password.toCharArray(),
                    null
            );
            session = connection.authenticate(auth);
            identity = requestedIdentity;
            return session;
        }

        synchronized void reset() {
            if (connection != null) {
                try {
                    connection.close();
                } catch (Exception ignored) {
                    // Reconnect on the next operation.
                }
            }
            if (client != null) {
                try {
                    client.close();
                } catch (Exception ignored) {
                    // Reconnect on the next operation.
                }
            }
            session = null;
            connection = null;
            client = null;
            identity = "";
        }

        void close() {
            reset();
        }
    }

    private static class DirectoryLoad {
        private final AtomicBoolean cancelled = new AtomicBoolean(false);
        private final AtomicReference<Connection> connection = new AtomicReference<>();
        volatile Future<?> future;

        boolean isCancelled() {
            return cancelled.get();
        }

        void attachConnection(Connection value) throws Exception {
            connection.set(value);
            if (cancelled.get()) {
                closeConnection();
                throw new InterruptedException("Directory loading was cancelled.");
            }
        }

        void detachConnection(Connection value) {
            connection.compareAndSet(value, null);
        }

        void cancel() {
            cancelled.set(true);
            closeConnection();
            Future<?> activeFuture = future;
            if (activeFuture != null) {
                activeFuture.cancel(true);
            }
        }

        void closeConnection() {
            Connection activeConnection = connection.getAndSet(null);
            if (activeConnection != null) {
                try {
                    activeConnection.close();
                } catch (Exception ignored) {
                    // Closing the SMB connection is best-effort during cancellation.
                }
            }
        }
    }

    private static class ThumbnailLoad {
        private final AtomicBoolean cancelled = new AtomicBoolean(false);
        private final AtomicReference<Connection> connection = new AtomicReference<>();
        volatile Future<?> future;

        boolean isCancelled() {
            return cancelled.get();
        }

        void attachConnection(Connection value) throws Exception {
            connection.set(value);
            if (cancelled.get()) {
                closeConnection();
                throw new InterruptedException("Thumbnail loading was cancelled.");
            }
        }

        void detachConnection(Connection value) {
            connection.compareAndSet(value, null);
        }

        void cancel() {
            cancelled.set(true);
            closeConnection();
            Future<?> activeFuture = future;
            if (activeFuture != null) {
                activeFuture.cancel(true);
            }
        }

        void closeConnection() {
            Connection activeConnection = connection.getAndSet(null);
            if (activeConnection != null) {
                try {
                    activeConnection.close();
                } catch (Exception ignored) {
                    // Closing the SMB connection is best-effort during cancellation.
                }
            }
        }
    }

    private static class DirectoryCacheEntry {
        final long savedAt;
        final List<RemoteItem> items;

        DirectoryCacheEntry(long savedAt, List<RemoteItem> items) {
            this.savedAt = savedAt;
            this.items = items;
        }
    }

    private static class NasConfig {
        final String host;
        final String user;
        final String password;

        NasConfig(String host, String user, String password) {
            this.host = host;
            this.user = user;
            this.password = password;
        }
    }

    private static class Credentials {
        final String user;
        final String password;

        Credentials(String user, String password) {
            this.user = user;
            this.password = password;
        }
    }

    private static class ResponsiveVideoView extends VideoView {
        private int videoWidth;
        private int videoHeight;

        ResponsiveVideoView(android.content.Context context) {
            super(context);
        }

        void setVideoSize(int width, int height) {
            videoWidth = width;
            videoHeight = height;
            requestLayout();
        }

        @Override
        protected void onMeasure(int widthMeasureSpec, int heightMeasureSpec) {
            int availableWidth = View.MeasureSpec.getSize(widthMeasureSpec);
            int availableHeight = View.MeasureSpec.getSize(heightMeasureSpec);
            if (videoWidth <= 0 || videoHeight <= 0 || availableWidth <= 0 || availableHeight <= 0) {
                setMeasuredDimension(availableWidth, availableHeight);
                return;
            }

            float videoRatio = (float) videoWidth / (float) videoHeight;
            float screenRatio = (float) availableWidth / (float) availableHeight;
            int measuredWidth;
            int measuredHeight;
            if (videoRatio > screenRatio) {
                measuredWidth = availableWidth;
                measuredHeight = Math.round(availableWidth / videoRatio);
            } else {
                measuredHeight = availableHeight;
                measuredWidth = Math.round(availableHeight * videoRatio);
            }
            setMeasuredDimension(measuredWidth, measuredHeight);
        }
    }

    private static class RemoteItem {
        final String share;
        final String name;
        final String path;
        final boolean directory;
        final boolean audioGroup;
        final int audioCount;

        RemoteItem(String share, String name, String path, boolean directory) {
            this(share, name, path, directory, false, 0);
        }

        RemoteItem(String share, String name, String path, boolean directory, boolean audioGroup, int audioCount) {
            this.share = share;
            this.name = name;
            this.path = path;
            this.directory = directory;
            this.audioGroup = audioGroup;
            this.audioCount = audioCount;
        }

        static RemoteItem audioFolder(String share, String name, String path, int count) {
            return new RemoteItem(share, name, path, true, true, count);
        }

        String displayName(boolean includePath) {
            if (audioGroup) {
                return name + " (" + audioCount + ")";
            }
            if (!includePath) {
                return name;
            }
            return share + "/" + path;
        }
    }

    private static class AudioFolderInfo {
        final String share;
        final String path;
        int count;

        AudioFolderInfo(String share, String path) {
            this.share = share;
            this.path = path;
        }
    }
}
