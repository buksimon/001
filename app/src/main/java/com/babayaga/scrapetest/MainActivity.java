package com.babayaga.scrapetest;

import android.app.Activity;
import android.app.DownloadManager;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.ContentValues;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.provider.MediaStore;
import android.text.InputType;
import android.view.Gravity;
import android.view.View;
import android.view.WindowManager;
import android.webkit.CookieManager;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Button;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Test app v1.0: Flashscore walker.
 *
 * Open: loads the link and tells you when the page is ready for scrap.
 *
 * Scrap, from a Flashscore match link with ?mid=:
 *  1. Main match: answer the age check YES, wait for "Page ready", then save
 *     SUMMARY (everything on the page except the odds), STATS (match, 1st half, 2nd half),
 *     LINEUPS, PLAYER STATS (every sub-tab, one line per player), COMMENTARY and REPORT.
 *  2. H2H tab (Overall): the 5 latest matches of the home team, the 5 latest of the away
 *     team and the 2 latest head-to-head matches. The main match itself is never taken
 *     from those lists. A match in more than one list is opened once and kept in each list.
 *  3. Each of those matches gets the same capture as step 1.
 *  4. A tab that is not in the page's tab row is "missing". A tab that is there but has no
 *     data is "empty". A match is complete when no tab is empty and its summary was captured.
 *
 * The screen shows only what is being scraped right now: the page and its percentage, and the
 * match counter. When the scrap ends it shows the marks and the unavailable tabs, saves one
 * JSON file in Downloads and posts a notification.
 *
 * Needs no assets. For the notification on Android 13+, add to AndroidManifest.xml:
 *   <uses-permission android:name="android.permission.POST_NOTIFICATIONS" />
 */
public class MainActivity extends Activity {

    // ---------------------------------------------------------------- theme

    private static final int BLACK = 0xFF000000;
    private static final int GREEN = 0xFF39FF6B;
    private static final int GREEN_HINT = 0x9939FF6B;
    private static final int GREEN_DIM = 0x3339FF6B;
    private static final int RED = 0xFFFF3B3B;
    private static final int WHITE = 0xFFFFFFFF;

    /** Matches to walk: the latest from each team's list and from the head-to-head list. */
    private static final int H2H_COUNT = 2;
    private static final int LAST_COUNT = 5;
    private static final int TARGET_TOTAL = H2H_COUNT + 2 * LAST_COUNT;

    private static final String CHANNEL_ID = "scrap_done";
    private static final int NOTIF_ID = 7;
    private static final int REQ_NOTIF = 11;

    /** The tab row at the top of a match page. Everything before it is the match header. */
    private static final String[] NAV_LABELS = {
            "MATCH", "REPORT", "ODDS", "H2H", "STANDINGS", "NEWS", "VIDEO",
            "SUMMARY", "STATS", "LINEUPS", "PLAYER STATS", "COMMENTARY"};

    /** Labels that belong to the odds block. The block is dropped. */
    private static final String[] ODDS_LABELS = {
            "ODDS", "1X2", "OVER/UNDER", "BOTH TEAMS TO SCORE", "DOUBLE CHANCE",
            "PLACE A BET", "BONUS OFFERS"};

    /** Single lines that are never data: ads, video, "show more" buttons. */
    private static final String[] NOISE_LINES = {
            "SKIP TO MAIN CONTENT", "ADVERTISEMENT", "AD", "SHOW MORE", "SHOW LESS",
            "SHOW FULL PREVIEW", "SHOW MORE MATCHES", "SHOW ALL STANDINGS", "VIDEO PREVIEW",
            "MATCH HIGHLIGHTS", "YOUTUBE", "1XBET"};

    /** Sub-tab and column labels. A tab that has only these (or "no data" lines) is empty. */
    private static final String[] SUB_LABELS = {
            "MATCH", "1ST HALF", "2ND HALF", "TOP STATS", "SHOTS", "ATTACK", "PASSES", "DEFENSE",
            "GOALKEEPING", "GENERAL", "ALL", "AVG. RATING", "MARKET VALUE", "AGE", "HEIGHT", "OVERALL"};

    /** Tab labels that must never be clicked as player-stats sub-tabs. */
    private static final String[] MAIN_TABS = {
            "ALL", "OVERALL", "SUMMARY", "STATS", "LINEUPS", "PLAYER STATS", "COMMENTARY", "REPORT",
            "ODDS", "H2H", "STANDINGS", "NEWS", "VIDEO", "MATCH", "1ST HALF", "2ND HALF"};

    private static final Pattern NO_DATA = Pattern.compile(
            "(?i)\\bno\\b.{0,40}\\b(data|statistics|stats|information|commentary|lineups?|events?|report|available)\\b"
          + "|not available|unavailable");

    // ---------------------------------------------------------------- page scripts

    /** Everything visible on the page, as text. */
    private static final String SNAP_JS =
            "(function(){return document.body?document.body.innerText:'';})()";

    /**
     * Page state for the "Page ready" check: a hash of the visible text (so we can see when it
     * stops changing), whether the match tabs are on screen, and whether the age check is up.
     */
    private static final String READY_JS =
            "(function(){try{"
          + "var s=document.body?document.body.innerText:'';"
          + "var h=0;for(var i=0;i<s.length;i++){h=((h<<5)-h+s.charCodeAt(i))|0;}"
          + "var u=s.toUpperCase();"
          + "return JSON.stringify({h:h,n:s.length,tabs:(u.indexOf('SUMMARY')>=0||u.indexOf('H2H')>=0),"
          + "age:(u.indexOf('LEGAL AGE')>=0)});"
          + "}catch(err){return JSON.stringify({h:0,n:0,tabs:false,age:false});}})()";

    /**
     * Finds the H2H tab's sections by their visible headings: HEAD-TO-HEAD MATCHES, and
     * LAST MATCHES: <team> (in page order, home team first). Rows are links that start with
     * a date. Any other all-caps heading ends the current section.
     */
    private static final String H2H_LIST_JS =
            "(function(){try{"
          + "var sections=[];var cur=null;var lastHeading='';var seen={};"
          + "var dateRe=/\\d{2}\\.\\d{2}\\.\\d{2}/;"
          + "var startRe=/^\\d{2}\\.\\d{2}\\.\\d{2}\\s+\\S/;"
          + "var all=document.querySelectorAll('*');"
          + "for(var i=0;i<all.length;i++){"
          + "var e=all[i];"
          + "var t=(e.textContent||'').replace(/\\s+/g,' ').trim();"
          + "if(t.length>0&&t.length<80&&t===t.toUpperCase()&&/[A-Z]{4,}/.test(t)){"
          + "if(t===lastHeading)continue;"
          + "lastHeading=t;"
          + "if(t.indexOf('HEAD-TO-HEAD')===0){cur={type:'h2h',name:'HEAD-TO-HEAD',rows:[],dates:0};sections.push(cur);}"
          + "else if(t.indexOf('LAST MATCHES')===0){cur={type:'last',name:t.replace(/^LAST MATCHES:?\\s*/,''),rows:[],dates:0};sections.push(cur);}"
          + "else{cur=null;}"
          + "continue;}"
          + "if(!cur)continue;"
          + "var it=(e.textContent||'').replace(/\\s+/g,' ').trim();"
          + "if(e.tagName==='A'&&dateRe.test(it)){"
          + "cur.rows.push({h:e.href||'',t:it.slice(0,160)});}"
          + "else if(!e.closest('a')&&startRe.test(it)&&!seen[it]){seen[it]=1;cur.dates++;}"
          + "}"
          + "return JSON.stringify({sections:sections});"
          + "}catch(err){return JSON.stringify({sections:[],err:String(err)});}})()";

    /** Clicks every visible "Show more matches" button. Returns how many it clicked. */
    private static final String SHOW_MORE_JS =
            "(function(){var c=document.querySelectorAll('a,button,span,div');var n=0;"
          + "for(var i=0;i<c.length;i++){var e=c[i];"
          + "var t=(e.innerText||'').trim().replace(/\\s+/g,' ').toLowerCase();"
          + "if(t==='show more matches'&&e.offsetParent!==null&&e.getElementsByTagName('*').length<3){e.click();n++;}}"
          + "return String(n);})()";

    /**
     * On a match page's PLAYER STATS view: the sub-tab labels sitting in the same row as
     * TOP STATS (the first sub-tab of PLAYER STATS).
     */
    private static final String PLAYER_SUBTABS_JS =
            "(function(){try{"
          + "var all=document.querySelectorAll('a,button,li,span,div,[role=tab]');"
          + "var anchor=null;"
          + "for(var i=0;i<all.length;i++){"
          + "var e=all[i];"
          + "var t=(e.innerText||'').trim().replace(/\\s+/g,' ').toUpperCase();"
          + "if(t==='TOP STATS'&&e.offsetParent!==null){anchor=e;break;}}"
          + "var out=[];"
          + "if(anchor&&anchor.parentElement){"
          + "var kids=anchor.parentElement.children;"
          + "for(var j=0;j<kids.length;j++){"
          + "var kt=(kids[j].innerText||'').trim().replace(/\\s+/g,' ');"
          + "if(kt&&kt.length<=24&&kt===kt.toUpperCase()&&/[A-Z]/.test(kt)&&out.indexOf(kt)<0){out.push(kt);}"
          + "}}"
          + "return JSON.stringify({labels:out});"
          + "}catch(err){return JSON.stringify({labels:[],err:String(err)});}})()";

    /**
     * Every visible table on the page, one line per row, cells joined with " | ".
     * A player cell keeps the position and the player id: "Name / Position #id".
     */
    private static final String TABLE_JS =
            "(function(){try{"
          + "var out=[];var tb=document.querySelectorAll('table');"
          + "for(var i=0;i<tb.length;i++){"
          + "if(tb[i].offsetParent===null)continue;"
          + "var rows=tb[i].querySelectorAll('tr');"
          + "for(var j=0;j<rows.length;j++){"
          + "var cells=rows[j].querySelectorAll('th,td');var v=[];"
          + "for(var k=0;k<cells.length;k++){var c=cells[k];"
          + "var b=c.querySelector('button');"
          + "var t=b?(b.textContent||''):(c.innerText||'');"
          + "t=t.split('\\n').map(function(x){return x.replace(/\\s+/g,' ').trim();})"
          + ".filter(function(x){return x;}).join(' / ');"
          + "var f=c.querySelector('[data-analytics-player-id]');"
          + "if(f)t+=' #'+f.getAttribute('data-analytics-player-id');"
          + "v.push(t);}"
          + "if(v.length)out.push(v.join(' | '));}"
          + "out.push('');}"
          + "return out.join('\\n');"
          + "}catch(err){return '';}})()";

    /**
     * Clicks a real tab of the page (the tab row, the stats, player stats and H2H sub-tabs) whose
     * visible text is exactly the given text. A heading with the same words is never clicked, so
     * "notfound" means the tab is not on the page.
     */
    private static final String CLICK_TAB_JS =
            "(function(txt){"
          + "var tabs=document.querySelectorAll('[data-testid=\"wcl-tab\"]');"
          + "for(var q=0;q<tabs.length;q++){var te=tabs[q];"
          + "var tt=(te.innerText||'').trim().replace(/\\s+/g,' ').toLowerCase();"
          + "if(tt===txt&&te.offsetParent!==null){te.scrollIntoView();te.click();return 'ok';}}"
          + "return 'notfound';})('__TXT__');";

    /** Clicks the smallest visible element whose visible text is exactly the given text. */
    private static final String CLICK_TEXT_JS =
            "(function(txt){"
          + "var c=document.querySelectorAll('a,button,li,span,div,[role=tab]');"
          + "var best=null;"
          + "for(var i=0;i<c.length;i++){var e=c[i];"
          + "var t=(e.innerText||'').trim().replace(/\\s+/g,' ').toLowerCase();"
          + "if(t!==txt||e.offsetParent===null)continue;"
          + "var n=e.getElementsByTagName('*').length;"
          + "if(!best||n<best.n)best={e:e,n:n};}"
          + "if(!best)return 'notfound';"
          + "best.e.scrollIntoView();best.e.click();return 'ok';})('__TXT__');";

    // ---------------------------------------------------------------- state

    private final Handler ui = new Handler(Looper.getMainLooper());
    private final StringBuilder logBuf = new StringBuilder();

    /** Every distinct match to open (a match in two lists is here once). */
    private final List<Rec> recs = new ArrayList<>();
    /** The matches in each list. The same Rec can be in more than one list. */
    private final List<Rec> homeSlots = new ArrayList<>();
    private final List<Rec> awaySlots = new ArrayList<>();
    private final List<Rec> h2hSlots = new ArrayList<>();
    private final List<String> pageNotes = new ArrayList<>();

    private EditText input;
    private Button scrapBtn;
    private TextView badge;
    private TextView statusView;
    private LinearLayout progressPanel;
    private TextView matchLabel;
    private TextView pageName;
    private TextView pagePct;
    private Bar pageBar;
    private LinearLayout counterBox;
    private TextView counterText;
    private TextView counterPct;
    private Bar counterBar;
    private LinearLayout resultPanel;
    private TextView marksView;
    private TextView unavailView;
    private WebView webView;
    private TextView logView;
    private ScrollView scroll;

    // walker state (all touched on the UI thread)
    private volatile boolean walking = false;
    private Runnable onLoaded;
    private int loadToken = 0;
    private int openToken = 0;
    private boolean awaitingReady = false;
    private String mid = "";
    private String matchUrl = "";
    private Rec mainRec;
    private int totalSlots = 0;
    private int doneSlots = 0;
    private String homeName = "Home";
    private String awayName = "Away";

    // the last saved result, for the Download button
    private String lastJson = "";
    private String lastName = "";
    private Uri lastSavedUri;

    /** One match page (the main match or one of the matches from the H2H tab). */
    private static class Rec {
        String mid = "";
        String url = "";
        String rowText = "";
        final List<String> groups = new ArrayList<>();   // home, away, h2h
        JSONObject tabs = new JSONObject();
        boolean summaryOk = false;
        boolean emptyFound = false;
        boolean done = false;
        boolean complete = false;
        final List<String> missing = new ArrayList<>();  // tab not in the tab row
        final List<String> emptyTabs = new ArrayList<>(); // tab there, no data
    }

    /** A thin progress bar: a filled part and the rest, sized by weight. */
    private static class Bar {
        LinearLayout track;
        View fill;
        View rest;
    }

    private interface Cb {
        void run(String s);
    }

    // ---------------------------------------------------------------- screen

    private static final String PREFS = "scrapetest";
    private static final String KEY_CRASH = "last_crash";

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        installCrashRecorder();
        try {
            buildScreen();
        } catch (Throwable t) {
            showStartupError(t);
        }
    }

    /** Saves the stack trace of any later crash, so the next launch can show it in the log. */
    private void installCrashRecorder() {
        final android.content.Context app = getApplicationContext();
        final Thread.UncaughtExceptionHandler old = Thread.getDefaultUncaughtExceptionHandler();
        Thread.setDefaultUncaughtExceptionHandler((th, ex) -> {
            try {
                app.getSharedPreferences(PREFS, MODE_PRIVATE).edit()
                        .putString(KEY_CRASH, android.util.Log.getStackTraceString(ex)).commit();
            } catch (Throwable ignored) {
                // nothing more can be done here
            }
            if (old != null) old.uncaughtException(th, ex);
        });
    }

    /** If the screen cannot be built, show the exact error instead of closing the app. */
    private void showStartupError(Throwable t) {
        String trace = android.util.Log.getStackTraceString(t);
        try {
            android.content.ClipboardManager cm =
                    (android.content.ClipboardManager) getSystemService(CLIPBOARD_SERVICE);
            if (cm != null) {
                cm.setPrimaryClip(android.content.ClipData.newPlainText("error", trace));
            }
        } catch (Throwable ignored) {
            // the copy is only a convenience
        }
        TextView tv = new TextView(this);
        tv.setText("BABAYAGA could not start.\nThe error is copied. Paste it in the chat.\n\n" + trace);
        tv.setTextColor(0xFF39FF6B);
        tv.setTextSize(13f);
        tv.setPadding(32, 64, 32, 32);
        ScrollView sv = new ScrollView(this);
        sv.setBackgroundColor(0xFF000000);
        sv.addView(tv);
        setContentView(sv);
    }

    private void buildScreen() {
        if (getActionBar() != null) getActionBar().hide();
        if (Build.VERSION.SDK_INT >= 21) getWindow().setStatusBarColor(BLACK);

        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(BLACK);
        root.setPadding(dp(16), dp(24), dp(16), dp(12));

        TextView title = new TextView(this);
        title.setText("BABAYAGA");
        title.setTextColor(GREEN);
        title.setTextSize(30f);
        title.setGravity(Gravity.CENTER);
        title.setTypeface(Typeface.DEFAULT_BOLD);
        root.addView(title, fullWidth(dp(16)));

        // link box: a long pill with a neon green ring
        input = new EditText(this);
        input.setHint("Paste a match link");
        input.setHintTextColor(GREEN_HINT);
        input.setTextColor(GREEN);
        input.setTextSize(16f);
        input.setInputType(InputType.TYPE_CLASS_TEXT);
        input.setSingleLine(true);
        input.setGravity(Gravity.CENTER_VERTICAL);
        input.setPadding(dp(22), dp(12), dp(22), dp(12));
        input.setBackground(pill(BLACK, GREEN, dp(30)));
        root.addView(input, fullWidth(dp(14)));

        // buttons: Open + Scrap on one row, Download + Clear on the next
        scrapBtn = makePill("Scrap", v -> {
            if (walking) stopWalk();
            else startWalk();
        });
        root.addView(buttonRow(makePill("Open", v -> openUrl()), scrapBtn), fullWidth(0));

        FrameLayout downloadWrap = new FrameLayout(this);
        downloadWrap.addView(makePill("Download", v -> {
            badge.setVisibility(View.GONE);
            downloadFile();
        }), new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT));
        badge = new TextView(this);
        badge.setText("1");
        badge.setTextColor(WHITE);
        badge.setTextSize(13f);
        badge.setGravity(Gravity.CENTER);
        badge.setPadding(0, 0, 0, 0);
        badge.setBackground(rounded(RED, dp(11)));
        badge.setVisibility(View.GONE);
        downloadWrap.addView(badge, new FrameLayout.LayoutParams(
                dp(22), dp(22), Gravity.END | Gravity.TOP));
        root.addView(buttonRow(downloadWrap, makePill("Clear", v -> clearAll())), fullWidth(dp(14)));

        // the current step, in plain words
        statusView = new TextView(this);
        statusView.setText("Ready. Paste a match link and tap Open or Scrap.");
        statusView.setTextColor(GREEN);
        statusView.setTextSize(17f);
        root.addView(statusView, fullWidth(dp(12)));

        // progress: only while scraping. The page being scraped and its percentage, then the
        // match counter once the H2H page has been read.
        progressPanel = new LinearLayout(this);
        progressPanel.setOrientation(LinearLayout.VERTICAL);
        progressPanel.setVisibility(View.GONE);

        matchLabel = new TextView(this);
        matchLabel.setTextColor(GREEN_HINT);
        matchLabel.setTextSize(14f);
        progressPanel.addView(matchLabel, fullWidth(dp(8)));

        LinearLayout pageRow = new LinearLayout(this);
        pageRow.setOrientation(LinearLayout.HORIZONTAL);
        pageName = new TextView(this);
        pageName.setTextColor(GREEN);
        pageName.setTextSize(20f);
        pageName.setTypeface(Typeface.DEFAULT_BOLD);
        pageRow.addView(pageName, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f));
        pagePct = new TextView(this);
        pagePct.setTextColor(GREEN);
        pagePct.setTextSize(20f);
        pagePct.setTypeface(Typeface.DEFAULT_BOLD);
        pageRow.addView(pagePct, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT));
        progressPanel.addView(pageRow, fullWidth(dp(4)));
        pageBar = makeBar();
        progressPanel.addView(pageBar.track, barParams(dp(16)));

        counterBox = new LinearLayout(this);
        counterBox.setOrientation(LinearLayout.VERTICAL);
        counterBox.setVisibility(View.GONE);
        LinearLayout counterRow = new LinearLayout(this);
        counterRow.setOrientation(LinearLayout.HORIZONTAL);
        counterText = new TextView(this);
        counterText.setTextColor(GREEN);
        counterText.setTextSize(20f);
        counterText.setTypeface(Typeface.DEFAULT_BOLD);
        counterRow.addView(counterText, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f));
        counterPct = new TextView(this);
        counterPct.setTextColor(GREEN);
        counterPct.setTextSize(20f);
        counterPct.setTypeface(Typeface.DEFAULT_BOLD);
        counterRow.addView(counterPct, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT));
        counterBox.addView(counterRow, fullWidth(dp(4)));
        counterBar = makeBar();
        counterBox.addView(counterBar.track, barParams(dp(8)));
        progressPanel.addView(counterBox, fullWidth(0));
        root.addView(progressPanel, fullWidth(dp(8)));

        // result: only when a scrap has ended
        resultPanel = new LinearLayout(this);
        resultPanel.setOrientation(LinearLayout.VERTICAL);
        resultPanel.setVisibility(View.GONE);
        marksView = new TextView(this);
        marksView.setTextColor(GREEN);
        marksView.setTextSize(18f);
        marksView.setTypeface(Typeface.MONOSPACE);
        resultPanel.addView(marksView, fullWidth(dp(14)));
        unavailView = new TextView(this);
        unavailView.setTextColor(GREEN_HINT);
        unavailView.setTextSize(14f);
        unavailView.setTextIsSelectable(true);
        resultPanel.addView(unavailView, fullWidth(0));
        root.addView(resultPanel, fullWidth(dp(8)));

        // the browser: hidden until Open or Scrap, then small and dimmed
        webView = new WebView(this);
        WebSettings s = webView.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setUserAgentString(s.getUserAgentString().replace("; wv", ""));
        CookieManager.getInstance().setAcceptCookie(true);
        CookieManager.getInstance().setAcceptThirdPartyCookies(webView, true);
        webView.setWebViewClient(new WebViewClient() {
            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                if (!walking && !"about:blank".equals(url)) log("Loaded: " + url);
                if (!walking && awaitingReady && !"about:blank".equals(url)) {
                    awaitingReady = false;
                    final int token = openToken;
                    status("Page loaded. Waiting for it to be ready...");
                    ui.postDelayed(() -> pollOpen(token, 0, -1, 0), 1000);
                }
                if (walking && onLoaded != null) {
                    final Runnable r = onLoaded;
                    onLoaded = null;
                    ui.postDelayed(() -> {
                        if (walking) r.run();
                    }, 3500);
                }
            }
        });
        LinearLayout.LayoutParams wlp = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, dp(160));
        wlp.topMargin = dp(12);
        root.addView(webView, wlp);
        webView.setVisibility(View.GONE);

        // log: fixed height, so it is never squeezed out of the screen
        scroll = new ScrollView(this);
        logView = new TextView(this);
        logView.setTextSize(12f);
        logView.setTextColor(GREEN);
        logView.setTextIsSelectable(true);
        scroll.addView(logView);
        root.addView(scroll, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, dp(200)));

        // the whole screen scrolls, so nothing is pushed off the bottom
        ScrollView page = new ScrollView(this);
        page.setBackgroundColor(BLACK);
        page.addView(root);
        setContentView(page);

        // Android 13+ asks before a notification can show.
        if (Build.VERSION.SDK_INT >= 33
                && checkSelfPermission("android.permission.POST_NOTIFICATIONS")
                != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(new String[] {"android.permission.POST_NOTIFICATIONS"}, REQ_NOTIF);
        }

        // If the app crashed last time, show where.
        String prevCrash = getSharedPreferences(PREFS, MODE_PRIVATE).getString(KEY_CRASH, "");
        if (!prevCrash.isEmpty()) {
            log("Last crash:\n" + prevCrash);
            getSharedPreferences(PREFS, MODE_PRIVATE).edit().remove(KEY_CRASH).apply();
        }

        // A link sent with another app's Share button: Flashscore links start the walk,
        // anything else just opens.
        Intent in = getIntent();
        if (in != null && Intent.ACTION_SEND.equals(in.getAction())) {
            String shared = in.getStringExtra(Intent.EXTRA_TEXT);
            if (shared != null) {
                input.setText(shared);
                log("Received shared text:\n" + shared);
                if (shared.contains("flashscore.") && shared.contains("mid=")) {
                    startWalk();
                } else {
                    openUrl();
                }
            }
        }
    }

    @Override
    public void onBackPressed() {
        if (webView != null && webView.getVisibility() == View.VISIBLE
                && webView.canGoBack() && !walking) {
            webView.goBack();
        } else {
            super.onBackPressed();
        }
    }

    // ---------------------------------------------------------------- theme helpers

    private int dp(int v) {
        return Math.round(v * getResources().getDisplayMetrics().density);
    }

    private GradientDrawable pill(int fill, int stroke, int radius) {
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.RECTANGLE);
        g.setColor(fill);
        g.setCornerRadius(radius);
        g.setStroke(dp(2), stroke);
        return g;
    }

    private GradientDrawable rounded(int color, int radius) {
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.RECTANGLE);
        g.setColor(color);
        g.setCornerRadius(radius);
        return g;
    }

    /** A green-outline pill with green text and no fill. */
    private Button makePill(String label, View.OnClickListener l) {
        Button b = new Button(this);
        b.setText(label);
        b.setAllCaps(false);
        b.setTextColor(GREEN);
        b.setTextSize(16f);
        b.setBackground(pill(0x00000000, GREEN, dp(22)));
        b.setMinHeight(dp(46));
        b.setOnClickListener(l);
        return b;
    }

    private LinearLayout buttonRow(View left, View right) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        addWeighted(row, left);
        addWeighted(row, right);
        return row;
    }

    private void addWeighted(LinearLayout row, View v) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f);
        lp.setMargins(dp(5), 0, dp(5), dp(10));
        row.addView(v, lp);
    }

    private LinearLayout.LayoutParams fullWidth(int bottomMargin) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT);
        lp.bottomMargin = bottomMargin;
        return lp;
    }

    private LinearLayout.LayoutParams barParams(int bottomMargin) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, dp(8));
        lp.bottomMargin = bottomMargin;
        return lp;
    }

    private Bar makeBar() {
        Bar b = new Bar();
        b.track = new LinearLayout(this);
        b.track.setOrientation(LinearLayout.HORIZONTAL);
        b.track.setWeightSum(100f);
        b.track.setBackground(rounded(GREEN_DIM, dp(4)));
        b.fill = new View(this);
        b.fill.setBackground(rounded(GREEN, dp(4)));
        b.rest = new View(this);
        b.track.addView(b.fill, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.MATCH_PARENT, 0f));
        b.track.addView(b.rest, new LinearLayout.LayoutParams(
                0, LinearLayout.LayoutParams.MATCH_PARENT, 100f));
        return b;
    }

    private void setBar(Bar b, int pct) {
        int p = Math.max(0, Math.min(100, pct));
        ((LinearLayout.LayoutParams) b.fill.getLayoutParams()).weight = p;
        ((LinearLayout.LayoutParams) b.rest.getLayoutParams()).weight = 100 - p;
        b.track.requestLayout();
    }

    /** The browser sits small and dimmed while a page loads or a scrape runs. */
    private void showBrowser() {
        webView.setVisibility(View.VISIBLE);
        webView.setAlpha(0.35f);
    }

    /** Shows a message in the status line and in the log. */
    private void status(final String msg) {
        ui.post(() -> statusView.setText(msg));
        log(msg);
    }

    /** The page being scraped and how far along it is. Shows only while scraping. */
    private void showPage(String name, int done, int total) {
        int pct = total <= 0 ? 0 : Math.min(100, done * 100 / total);
        progressPanel.setVisibility(View.VISIBLE);
        pageName.setText(name);
        pagePct.setText(pct + "%");
        setBar(pageBar, pct);
    }

    private void updateCounter() {
        counterBox.setVisibility(View.VISIBLE);
        int pct = totalSlots <= 0 ? 0 : Math.min(100, doneSlots * 100 / totalSlots);
        counterText.setText("Matches " + doneSlots + " / " + totalSlots);
        counterPct.setText(pct + "%");
        setBar(counterBar, pct);
    }

    private void resetPanels() {
        progressPanel.setVisibility(View.GONE);
        counterBox.setVisibility(View.GONE);
        resultPanel.setVisibility(View.GONE);
        matchLabel.setText("");
        setBar(pageBar, 0);
        setBar(counterBar, 0);
    }

    // ---------------------------------------------------------------- buttons

    /** Loads the link and says when the page is ready for scrap. */
    private void openUrl() {
        if (walking) {
            status("A scrap is running. Tap Stop first.");
            return;
        }
        String text = input.getText().toString();
        Matcher m = Pattern.compile("https?://\\S+").matcher(text);
        if (!m.find()) {
            status("No link found in the box. Paste a match link first.");
            return;
        }
        String url = m.group();
        status("Opening the page...");
        showBrowser();
        openToken++;
        awaitingReady = true;
        webView.loadUrl(url);
    }

    /** After Open: waits until the page stops changing, then says it is ready for scrap. */
    private void pollOpen(final int token, final int tries, final int lastHash, final int stable) {
        if (token != openToken || walking) return;
        webView.evaluateJavascript(READY_JS, v -> {
            if (token != openToken || walking) return;
            JSONObject o = parseOrEmpty(unquote(v));
            final int h = o.optInt("h");
            int n = o.optInt("n");
            boolean tabsShown = o.optBoolean("tabs");
            if (o.optBoolean("age")) {
                log("Age check on screen: answering YES");
                webView.evaluateJavascript(clickText("yes"), null);
                ui.postDelayed(() -> pollOpen(token, tries + 1, -1, 0), 1000);
                return;
            }
            final int nextStable = (tabsShown && n > 0 && h == lastHash) ? stable + 1 : 0;
            if (nextStable >= 4) {
                status("Page ready ✓  Tap Scrap to start.");
                return;
            }
            if (tries >= 60) {
                status("The page opened but did not settle. You can still tap Scrap.");
                return;
            }
            ui.postDelayed(() -> pollOpen(token, tries + 1, h, nextStable), 500);
        });
    }

    /**
     * Download: the file is saved to Downloads as soon as the walk finishes, so this only
     * confirms it (or saves it again if that first save failed). No share sheet.
     */
    private void downloadFile() {
        if (lastJson.isEmpty()) {
            status("Nothing to download yet. Tap Scrap first.");
            return;
        }
        if (lastSavedUri != null) {
            status("Already in Downloads: " + lastName);
            return;
        }
        saveToDownloads(lastName, lastJson);
        if (lastSavedUri != null) {
            status("Saved to Downloads: " + lastName);
        } else {
            status("Could not save to Downloads. Check the log.");
        }
    }

    /** Clears the link box, the log, the progress and the browser. Stops a running scrape first. */
    private void clearAll() {
        if (walking) stopWalk();
        openToken++;
        awaitingReady = false;
        input.setText("");
        synchronized (logBuf) {
            logBuf.setLength(0);
        }
        logView.setText("");
        resetData();
        lastJson = "";
        lastName = "";
        lastSavedUri = null;
        badge.setVisibility(View.GONE);
        resetPanels();
        webView.loadUrl("about:blank");
        webView.setVisibility(View.GONE);
        status("Cleared. Paste a match link and tap Open or Scrap.");
    }

    private void resetData() {
        recs.clear();
        homeSlots.clear();
        awaySlots.clear();
        h2hSlots.clear();
        pageNotes.clear();
        mainRec = null;
        totalSlots = 0;
        doneSlots = 0;
        homeName = "Home";
        awayName = "Away";
    }

    // ---------------------------------------------------------------- the walker

    private void startWalk() {
        if (walking) {
            status("Already scrapping. Tap Stop first.");
            return;
        }
        String text = input.getText().toString();
        Matcher u = Pattern.compile("https?://\\S+").matcher(text);
        if (!u.find()) {
            status("Scrap needs a Flashscore match link that has ?mid= in it.");
            return;
        }
        matchUrl = u.group();
        Matcher mm = Pattern.compile("[?&]mid=([A-Za-z0-9]+)").matcher(matchUrl);
        if (!matchUrl.contains("flashscore.") || !mm.find()) {
            status("Scrap needs a Flashscore match link that has ?mid= in it.");
            return;
        }
        mid = mm.group(1);

        openToken++;
        awaitingReady = false;
        resetData();
        mainRec = new Rec();
        mainRec.mid = mid;
        mainRec.url = matchUrl;
        badge.setVisibility(View.GONE);
        resetPanels();

        walking = true;
        scrapBtn.setText("Stop");
        showBrowser();
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        matchLabel.setText("Main match");
        showPage("Opening the page", 0, 1);
        status("Scrap started for " + mid + ". Keep the app open until it says done.");
        loadThen(matchUrl, this::walkMain);
    }

    private void stopWalk() {
        if (!walking) {
            status("Not scrapping.");
            return;
        }
        status("Stopped by you. Saving what was collected so far.");
        finishWalk(false);
    }

    /** Loads a page, then runs next a few seconds after it finishes loading. */
    private void loadThen(String url, Runnable next) {
        if (!walking) return;
        final int token = ++loadToken;
        onLoaded = next;
        webView.loadUrl(url);
        ui.postDelayed(() -> {
            if (walking && token == loadToken && onLoaded != null) {
                Runnable r = onLoaded;
                onLoaded = null;
                log("   (page slow, continuing anyway)");
                r.run();
            }
        }, 30000);
    }

    private void jsWalk(String script, Cb cb) {
        if (!walking) return;
        webView.evaluateJavascript(script, v -> {
            if (walking) cb.run(unquote(v));
        });
    }

    /**
     * Waits until the page's visible text stops changing for about 2 seconds, with the
     * match tabs on screen. Answers the age check YES if it shows up. If label is not null,
     * shows "Page ready: label" when the page has settled.
     */
    private void waitSettled(String label, Runnable done) {
        waitReady(0, -1, 0, label, label != null ? 60 : 24, done);
    }

    private void waitReady(final int tries, final int lastHash, final int stable,
                           final String label, final int maxTries, final Runnable done) {
        if (!walking) return;
        jsWalk(READY_JS, json -> {
            final JSONObject o = parseOrEmpty(json);
            final int h = o.optInt("h");
            final int n = o.optInt("n");
            final boolean tabsShown = o.optBoolean("tabs");
            final boolean ageAsked = o.optBoolean("age");
            if (ageAsked) {
                log("Age check on screen: answering YES");
                tryClick("yes", 0, 3, false, res -> {
                    ui.postDelayed(() -> waitReady(tries + 1, -1, 0, label, maxTries, done), 800);
                });
                return;
            }
            final int nextStable = (tabsShown && n > 0 && h == lastHash) ? stable + 1 : 0;
            if (nextStable >= 4) {
                if (label != null) status("Page ready ✓ " + label);
                done.run();
                return;
            }
            if (tries >= maxTries) {
                log("Page did not settle in time. Continuing with what is on screen.");
                done.run();
                return;
            }
            ui.postDelayed(() -> waitReady(tries + 1, h, nextStable, label, maxTries, done), 500);
        });
    }

    /**
     * Clicks the tab with this visible text. If it is not on the page yet, tries again
     * once a second, up to maxTries times. Calls done with "ok" or "notfound".
     */
    private void waitClick(final String txt, final int maxTries, final Cb done) {
        tryClick(txt, 0, maxTries, true, done);
    }

    private void tryClick(final String txt, final int tries, final int maxTries,
                          final boolean tabOnly, final Cb done) {
        if (!walking) return;
        jsWalk(tabOnly ? clickTab(txt) : clickText(txt), res -> {
            if ("ok".equals(res) || tries + 1 >= maxTries) {
                done.run(res);
            } else {
                ui.postDelayed(() -> tryClick(txt, tries + 1, maxTries, tabOnly, done), 1000);
            }
        });
    }

    // ---- step 1 and 3: capture one match page

    /** Captures SUMMARY, STATS, LINEUPS, PLAYER STATS, COMMENTARY and REPORT on the page that is open. */
    private void captureRecord(final Rec r, final String label, final Runnable done) {
        showPage("Waiting for the page", 0, 1);
        waitSettled(label, () -> {
            showPage("Summary", 0, 1);
            jsWalk(SNAP_JS, raw -> {
                String body = cleanPage(raw, false);
                r.summaryOk = !isEmptyBody(body);
                if (!r.summaryOk) r.emptyTabs.add("Summary");
                jput(r.tabs, "summary", leaf(r.summaryOk ? "captured" : "empty", cleanPage(raw, true)));
                showPage("Summary", 1, 1);
                stepStats(r, () -> stepLineups(r, () -> stepPlayerStats(r,
                        () -> stepCommentary(r, () -> stepReport(r, done)))));
            });
        });
    }

    /** STATS: the MATCH view, then 1ST HALF and 2ND HALF. */
    private void stepStats(final Rec r, final Runnable next) {
        final JSONObject stats = new JSONObject();
        waitClick("stats", 2, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, r.tabs, "stats", "Stats");
                next.run();
                return;
            }
            jput(r.tabs, "stats", stats);
            showPage("Stats", 0, 3);
            waitSettled(null, () -> jsWalk(SNAP_JS, raw -> {
                putBody(r, stats, "match", "Stats / match", raw);
                showPage("Stats", 1, 3);
                statSub(r, stats, "1st half", "first_half", "Stats / 1st half", 2,
                        () -> statSub(r, stats, "2nd half", "second_half", "Stats / 2nd half", 3, next));
            }));
        });
    }

    private void statSub(final Rec r, final JSONObject parent, final String clickLabel,
                         final String key, final String name, final int step, final Runnable next) {
        waitClick(clickLabel, 3, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, parent, key, name);
                showPage("Stats", step, 3);
                next.run();
                return;
            }
            waitSettled(null, () -> jsWalk(SNAP_JS, raw -> {
                putBody(r, parent, key, name, raw);
                showPage("Stats", step, 3);
                next.run();
            }));
        });
    }

    /**
     * LINEUPS: on a finished match the ratings are already in the page. On a match that has
     * not been played, AVG. RATING is clicked once if it is there.
     */
    private void stepLineups(final Rec r, final Runnable next) {
        waitClick("lineups", 2, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, r.tabs, "lineups", "Lineups");
                next.run();
                return;
            }
            showPage("Lineups", 0, 1);
            waitSettled(null, () -> waitClick("avg. rating", 1, ar -> {
                waitSettled(null, () -> jsWalk(SNAP_JS, raw -> {
                    putBody(r, r.tabs, "lineups", "Lineups", raw);
                    showPage("Lineups", 1, 1);
                    next.run();
                }));
            }));
        });
    }

    /** PLAYER STATS: every sub-tab the page shows, one line per player. */
    private void stepPlayerStats(final Rec r, final Runnable next) {
        waitClick("player stats", 2, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, r.tabs, "player_stats", "Player stats");
                next.run();
                return;
            }
            final JSONObject ps = new JSONObject();
            jput(r.tabs, "player_stats", ps);
            showPage("Player stats", 0, 1);
            waitSettled(null, () -> jsWalk(PLAYER_SUBTABS_JS, json -> {
                final List<String> labels = subTabLabels(json);
                if (labels.isEmpty()) {
                    jsWalk(TABLE_JS, table -> {
                        putTable(r, ps, "default", "Player stats", table);
                        showPage("Player stats", 1, 1);
                        next.run();
                    });
                    return;
                }
                log("   player stats sub-tabs: " + labels);
                subTabs(r, ps, labels, 0, next);
            }));
        });
    }

    private void subTabs(final Rec r, final JSONObject ps, final List<String> labels,
                         final int i, final Runnable next) {
        if (i >= labels.size()) {
            next.run();
            return;
        }
        final String label = labels.get(i);
        final String key = keyOf(label);
        final String shown = "Player stats · " + titleCase(label);
        showPage(shown, i, labels.size());
        waitClick(label.toLowerCase(Locale.ROOT), 3, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, ps, key, "Player stats / " + titleCase(label));
                subTabs(r, ps, labels, i + 1, next);
                return;
            }
            waitSettled(null, () -> jsWalk(TABLE_JS, table -> {
                putTable(r, ps, key, "Player stats / " + titleCase(label), table);
                showPage(shown, i + 1, labels.size());
                subTabs(r, ps, labels, i + 1, next);
            }));
        });
    }

    /** COMMENTARY: the text of the tab as shown. */
    private void stepCommentary(final Rec r, final Runnable next) {
        waitClick("commentary", 2, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, r.tabs, "commentary", "Commentary");
                next.run();
                return;
            }
            showPage("Commentary", 0, 1);
            waitSettled(null, () -> jsWalk(SNAP_JS, raw -> {
                putBody(r, r.tabs, "commentary", "Commentary", raw);
                showPage("Commentary", 1, 1);
                next.run();
            }));
        });
    }

    /** REPORT: the article page. */
    private void stepReport(final Rec r, final Runnable next) {
        waitClick("report", 2, res -> {
            if (!"ok".equals(res)) {
                putMissing(r, r.tabs, "report", "Report");
                next.run();
                return;
            }
            showPage("Report", 0, 1);
            waitSettled(null, () -> jsWalk(SNAP_JS, raw -> {
                putBody(r, r.tabs, "report", "Report", raw);
                showPage("Report", 1, 1);
                next.run();
            }));
        });
    }

    private void finishRecord(Rec r) {
        r.done = true;
        r.complete = r.summaryOk && !r.emptyFound;
        log((r == mainRec ? "Main match" : "Match") + ": " + (r.complete ? "complete" : "incomplete")
                + (r.missing.isEmpty() ? "" : "  (not on page: " + join(r.missing) + ")")
                + (r.emptyTabs.isEmpty() ? "" : "  (empty: " + join(r.emptyTabs) + ")"));
        if (r != mainRec) {
            doneSlots += r.groups.size();
            updateCounter();
        }
    }

    // ---- step 1: the main match, then the H2H tab

    private void walkMain() {
        matchLabel.setText("Main match");
        captureRecord(mainRec, "main match", () -> {
            finishRecord(mainRec);
            stepH2H();
        });
    }

    private void stepH2H() {
        status("Opening the H2H tab...");
        matchLabel.setText("Main match");
        showPage("H2H", 0, 1);
        waitClick("h2h", 20, res -> {
            if (!"ok".equals(res)) {
                status("H2H tab not found. Only the main match was saved.");
                pageNotes.add("H2H tab not found on the main match page.");
                finishWalk(true);
                return;
            }
            waitSettled(null, () -> waitClick("overall", 3, o -> {
                waitSettled(null, () -> pollH2H(0, false));
            }));
        });
    }

    /** Waits for the H2H sections to render, then reads them. */
    private void pollH2H(final int tries, final boolean moreTried) {
        if (!walking) return;
        jsWalk(H2H_LIST_JS, json -> {
            JSONObject o = parseOrEmpty(json);
            JSONArray secs = o.optJSONArray("sections");
            int lastCount = 0;
            boolean h2h = false;
            if (secs != null) {
                for (int i = 0; i < secs.length(); i++) {
                    JSONObject s = secs.optJSONObject(i);
                    if (s == null) continue;
                    String type = s.optString("type");
                    if ("h2h".equals(type)) h2h = true;
                    if ("last".equals(type)) lastCount++;
                }
            }
            if ((h2h && lastCount >= 2) || tries >= 15) {
                processSections(o, moreTried);
            } else {
                ui.postDelayed(() -> pollH2H(tries + 1, moreTried), 1000);
            }
        });
    }

    /**
     * Takes the latest LAST_COUNT matches of each team and H2H_COUNT head-to-head matches.
     * The main match is skipped, and a match in more than one list is opened once.
     */
    private void processSections(JSONObject o, boolean moreTried) {
        JSONArray secs = o.optJSONArray("sections");
        JSONObject h2hSec = null;
        List<JSONObject> lastSecs = new ArrayList<>();
        if (secs != null) {
            for (int i = 0; i < secs.length(); i++) {
                JSONObject s = secs.optJSONObject(i);
                if (s == null) continue;
                String type = s.optString("type");
                if ("h2h".equals(type) && h2hSec == null) {
                    h2hSec = s;
                } else if ("last".equals(type)) {
                    lastSecs.add(s);
                }
            }
        }
        JSONObject homeSec = lastSecs.size() >= 1 ? lastSecs.get(0) : null;
        JSONObject awaySec = lastSecs.size() >= 2 ? lastSecs.get(1) : null;

        Map<String, Rec> byMid = new LinkedHashMap<>();
        List<Rec> h2hSel = select(h2hSec, H2H_COUNT, "h2h", byMid);
        List<Rec> homeSel = select(homeSec, LAST_COUNT, "home", byMid);
        List<Rec> awaySel = select(awaySec, LAST_COUNT, "away", byMid);

        // Short of matches (the main match was skipped, say): open "Show more matches" once.
        boolean short5 = (h2hSec != null && h2hSel.size() < H2H_COUNT)
                || (homeSec != null && homeSel.size() < LAST_COUNT)
                || (awaySec != null && awaySel.size() < LAST_COUNT);
        if (short5 && !moreTried) {
            jsWalk(SHOW_MORE_JS, n -> {
                if (!n.isEmpty() && !"0".equals(n)) {
                    log("Opened " + n + " 'Show more matches' button(s).");
                    ui.postDelayed(() -> pollH2H(0, true), 1500);
                } else {
                    processSections(o, true);
                }
            });
            return;
        }

        if (homeSec != null) {
            String n = homeSec.optString("name").trim();
            homeName = n.isEmpty() ? "Home" : n;
        }
        if (awaySec != null) {
            String n = awaySec.optString("name").trim();
            awayName = n.isEmpty() ? "Away" : n;
        }
        if (h2hSec == null) pageNotes.add("HEAD-TO-HEAD MATCHES section not found.");
        if (homeSec == null) pageNotes.add("LAST MATCHES section for the home team not found.");
        if (awaySec == null) pageNotes.add("LAST MATCHES section for the away team not found.");
        if (h2hSec != null && h2hSel.size() < H2H_COUNT) {
            pageNotes.add("Only " + h2hSel.size() + " of " + H2H_COUNT + " head-to-head matches on the page.");
        }
        if (homeSec != null && homeSel.size() < LAST_COUNT) {
            pageNotes.add("Only " + homeSel.size() + " of " + LAST_COUNT + " matches for " + homeName + ".");
        }
        if (awaySec != null && awaySel.size() < LAST_COUNT) {
            pageNotes.add("Only " + awaySel.size() + " of " + LAST_COUNT + " matches for " + awayName + ".");
        }

        recs.clear();
        recs.addAll(byMid.values());
        h2hSlots.clear();
        h2hSlots.addAll(h2hSel);
        homeSlots.clear();
        homeSlots.addAll(homeSel);
        awaySlots.clear();
        awaySlots.addAll(awaySel);
        totalSlots = h2hSel.size() + homeSel.size() + awaySel.size();
        doneSlots = 0;
        updateCounter();
        status("Found " + totalSlots + " matches to scrap (" + recs.size() + " pages to open): "
                + homeSel.size() + " " + homeName + ", " + awaySel.size() + " " + awayName
                + ", " + h2hSel.size() + " H2H.");
        if (recs.isEmpty()) {
            finishWalk(true);
            return;
        }
        nextRec(0);
    }

    /** The first max matches of a section, without the main match and without repeats. */
    private List<Rec> select(JSONObject sec, int max, String group, Map<String, Rec> byMid) {
        List<Rec> out = new ArrayList<>();
        if (sec == null) return out;
        JSONArray rows = sec.optJSONArray("rows");
        if (rows == null) return out;
        Set<String> seen = new HashSet<>();
        for (int i = 0; i < rows.length() && out.size() < max; i++) {
            JSONObject row = rows.optJSONObject(i);
            if (row == null) continue;
            String href = row.optString("h");
            String text = row.optString("t");
            String id = midOf(href);
            if (href.isEmpty() || id.isEmpty()) {
                log("Row has no link, skipped: " + shorten(text));
                continue;
            }
            if (id.equals(mid)) {
                log("Skipped (this is the main match): " + shorten(text));
                continue;
            }
            if (!seen.add(id)) continue;
            Rec r = byMid.get(id);
            if (r == null) {
                r = new Rec();
                r.mid = id;
                r.url = href;
                r.rowText = text;
                byMid.put(id, r);
            }
            r.groups.add(group);
            out.add(r);
        }
        return out;
    }

    /** Opens the next match from the H2H tab and captures it. */
    private void nextRec(final int i) {
        if (!walking) return;
        if (i >= recs.size()) {
            finishWalk(true);
            return;
        }
        final Rec r = recs.get(i);
        matchLabel.setText(groupLabel(r) + "  ·  " + shorten(r.rowText));
        showPage("Opening the page", 0, 1);
        status("Opening match " + (i + 1) + " of " + recs.size() + ": " + shorten(r.rowText));
        loadThen(r.url, () -> captureRecord(r, shorten(r.rowText), () -> {
            finishRecord(r);
            nextRec(i + 1);
        }));
    }

    private String groupLabel(Rec r) {
        List<String> names = new ArrayList<>();
        for (String g : r.groups) {
            if ("home".equals(g)) names.add(homeName);
            else if ("away".equals(g)) names.add(awayName);
            else names.add("H2H");
        }
        return join(names, " + ");
    }

    // ---- finishing

    /** Stops the walk, saves whatever was collected, shows the marks and, if asked, notifies. */
    private void finishWalk(boolean notify) {
        if (!walking) return;
        walking = false;
        onLoaded = null;
        getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        scrapBtn.setText("Scrap");
        progressPanel.setVisibility(View.GONE);
        if (mainRec == null) return;

        int home = countComplete(homeSlots);
        int away = countComplete(awaySlots);
        int h2h = countComplete(h2hSlots);
        int overall = home + away + h2h;

        JSONObject out = new JSONObject();
        jput(out, "mid", mid);
        jput(out, "match_url", matchUrl);

        JSONObject mainObj = new JSONObject();
        jput(mainObj, "complete", mainRec.complete);
        jput(mainObj, "tabs", mainRec.tabs);
        jput(mainObj, "not_on_page", toArray(mainRec.missing));
        jput(mainObj, "empty", toArray(mainRec.emptyTabs));
        jput(out, "main_match", mainObj);

        JSONArray h2hArr = new JSONArray();
        for (Rec r : h2hSlots) h2hArr.put(recJson(r));
        JSONArray homeArr = new JSONArray();
        for (Rec r : homeSlots) homeArr.put(recJson(r));
        JSONArray awayArr = new JSONArray();
        for (Rec r : awaySlots) awayArr.put(recJson(r));
        jput(out, "h2h", h2hArr);

        JSONObject homeObj = new JSONObject();
        jput(homeObj, "name", homeName);
        jput(homeObj, "matches", homeArr);
        JSONObject awayObj = new JSONObject();
        jput(awayObj, "name", awayName);
        jput(awayObj, "matches", awayArr);
        JSONObject last = new JSONObject();
        jput(last, "home_team", homeObj);
        jput(last, "away_team", awayObj);
        jput(out, "last_matches", last);

        JSONObject marks = new JSONObject();
        jput(marks, "overall", overall);
        jput(marks, "overall_of", TARGET_TOTAL);
        jput(marks, "home", home);
        jput(marks, "home_of", LAST_COUNT);
        jput(marks, "away", away);
        jput(marks, "away_of", LAST_COUNT);
        jput(marks, "h2h", h2h);
        jput(marks, "h2h_of", H2H_COUNT);
        jput(marks, "main_match_complete", mainRec.complete);
        jput(out, "marks", marks);

        String unavailable = unavailableText();
        jput(out, "unavailable", unavailableJson());
        jput(out, "notes", toArray(pageNotes));
        jput(out, "complete_count", overall);
        jput(out, "total_count", totalSlots);
        jput(out, "collected_at", System.currentTimeMillis());

        String json;
        try {
            json = out.toString(1);
        } catch (JSONException e) {
            json = out.toString();
        }
        lastJson = json;
        lastName = "flashscore_" + mid + "_" + (System.currentTimeMillis() / 1000) + ".json";
        lastSavedUri = null;
        saveToDownloads(lastName, json);
        badge.setVisibility(View.VISIBLE);

        StringBuilder m = new StringBuilder();
        m.append(markLine("Overall", overall, TARGET_TOTAL)).append('\n');
        m.append(markLine(shorten(homeName, 9), home, LAST_COUNT)).append('\n');
        m.append(markLine(shorten(awayName, 9), away, LAST_COUNT)).append('\n');
        m.append(markLine("H2H", h2h, H2H_COUNT)).append('\n');
        m.append("Main match  ").append(mainRec.complete ? "complete ✓" : "incomplete !");
        marksView.setText(m.toString());
        unavailView.setText(unavailable.isEmpty()
                ? "Unavailable tabs: none"
                : "Unavailable tabs\n" + unavailable);
        resultPanel.setVisibility(View.VISIBLE);

        String summary = overall + " of " + TARGET_TOTAL + " matches complete";
        status("Done: " + summary + ". Main match "
                + (mainRec.complete ? "complete" : "incomplete") + "."
                + (lastSavedUri != null ? " Saved to Downloads: " + lastName : ""));
        if (notify) {
            notifyDone("Scrap finished", summary + ". Tap to open Downloads.");
        }
    }

    private static int countComplete(List<Rec> list) {
        int n = 0;
        for (Rec r : list) {
            if (r.complete) n++;
        }
        return n;
    }

    private static String markLine(String name, int ok, int total) {
        return String.format(Locale.US, "%-9s %2d / %-2d %s", name, ok, total,
                ok >= total ? "✓" : "!");
    }

    /** One block per match that has a tab that is not on its page, empty, or not scraped. */
    private String unavailableText() {
        StringBuilder sb = new StringBuilder();
        for (String n : pageNotes) sb.append("- ").append(n).append('\n');
        appendUnavailable(sb, "Main match", mainRec);
        for (Rec r : h2hSlots) appendUnavailable(sb, "H2H: " + shorten(r.rowText), r);
        for (Rec r : homeSlots) appendUnavailable(sb, homeName + ": " + shorten(r.rowText), r);
        for (Rec r : awaySlots) appendUnavailable(sb, awayName + ": " + shorten(r.rowText), r);
        return sb.toString().trim();
    }

    private static void appendUnavailable(StringBuilder sb, String title, Rec r) {
        if (r == null) return;
        if (r.done && r.missing.isEmpty() && r.emptyTabs.isEmpty()) return;
        sb.append(title).append('\n');
        if (!r.done) sb.append("   not scraped\n");
        if (!r.missing.isEmpty()) sb.append("   not on the page: ").append(join(r.missing)).append('\n');
        if (!r.emptyTabs.isEmpty()) sb.append("   empty: ").append(join(r.emptyTabs)).append('\n');
    }

    private JSONArray unavailableJson() {
        JSONArray arr = new JSONArray();
        addUnavailable(arr, "main", "Main match", mainRec);
        for (Rec r : h2hSlots) addUnavailable(arr, "h2h", r.rowText, r);
        for (Rec r : homeSlots) addUnavailable(arr, "home", r.rowText, r);
        for (Rec r : awaySlots) addUnavailable(arr, "away", r.rowText, r);
        return arr;
    }

    private static void addUnavailable(JSONArray arr, String group, String title, Rec r) {
        if (r == null) return;
        if (r.done && r.missing.isEmpty() && r.emptyTabs.isEmpty()) return;
        JSONObject o = new JSONObject();
        jput(o, "group", group);
        jput(o, "match", title);
        jput(o, "mid", r.mid);
        jput(o, "scraped", r.done);
        jput(o, "not_on_page", toArray(r.missing));
        jput(o, "empty", toArray(r.emptyTabs));
        arr.put(o);
    }

    private JSONObject recJson(Rec r) {
        JSONObject o = new JSONObject();
        jput(o, "mid", r.mid);
        jput(o, "url", r.url);
        jput(o, "row_text", r.rowText);
        jput(o, "also_in", toArray(r.groups));
        jput(o, "done", r.done);
        jput(o, "complete", r.complete);
        jput(o, "not_on_page", toArray(r.missing));
        jput(o, "empty", toArray(r.emptyTabs));
        jput(o, "tabs", r.tabs);
        return o;
    }

    private void saveToDownloads(String name, String body) {
        if (Build.VERSION.SDK_INT < 29) {
            save(name, body);
            log("Saved in the app's files folder only (this Android is older than 10).");
            return;
        }
        try {
            ContentValues v = new ContentValues();
            v.put(MediaStore.MediaColumns.DISPLAY_NAME, name);
            v.put(MediaStore.MediaColumns.MIME_TYPE, "application/json");
            v.put(MediaStore.MediaColumns.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS);
            Uri uri = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, v);
            if (uri == null) {
                log("Could not create the file in Downloads.");
                return;
            }
            OutputStream os = getContentResolver().openOutputStream(uri);
            if (os == null) {
                log("Could not open the file in Downloads.");
                return;
            }
            os.write(body.getBytes(StandardCharsets.UTF_8));
            os.close();
            lastSavedUri = uri;
            log("Saved to Downloads: " + name);
        } catch (Exception e) {
            log("Saving to Downloads failed: " + e);
        }
    }

    /** A notification that opens the Downloads app when it is tapped. */
    private void notifyDone(String title, String text) {
        try {
            NotificationManager nm = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
            if (nm == null) return;
            Notification.Builder b;
            if (Build.VERSION.SDK_INT >= 26) {
                NotificationChannel ch = new NotificationChannel(
                        CHANNEL_ID, "Scrap finished", NotificationManager.IMPORTANCE_HIGH);
                nm.createNotificationChannel(ch);
                b = new Notification.Builder(this, CHANNEL_ID);
            } else {
                b = new Notification.Builder(this);
            }
            Intent open = new Intent(DownloadManager.ACTION_VIEW_DOWNLOADS);
            open.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            int flags = PendingIntent.FLAG_UPDATE_CURRENT;
            if (Build.VERSION.SDK_INT >= 23) flags |= PendingIntent.FLAG_IMMUTABLE;
            PendingIntent pi = PendingIntent.getActivity(this, 0, open, flags);
            b.setSmallIcon(android.R.drawable.stat_sys_download_done)
                    .setContentTitle(title)
                    .setContentText(text)
                    .setContentIntent(pi)
                    .setAutoCancel(true);
            nm.notify(NOTIF_ID, b.build());
        } catch (Exception e) {
            log("Could not show the notification: " + e);
        }
    }

    // ---------------------------------------------------------------- tab records

    private JSONObject leaf(String status, String text) {
        JSONObject o = new JSONObject();
        jput(o, "status", status);
        jput(o, "text", text);
        return o;
    }

    /** Records a tab: captured if it has data, empty if not. */
    private void putLeaf(Rec r, JSONObject parent, String key, String name, String text, boolean empty) {
        if (empty) {
            r.emptyFound = true;
            r.emptyTabs.add(name);
        }
        jput(parent, key, leaf(empty ? "empty" : "captured", text));
    }

    /** Records a tab from the page text, cleaned (no header, odds, ads, news or footer). */
    private void putBody(Rec r, JSONObject parent, String key, String name, String raw) {
        String body = cleanPage(raw, false);
        putLeaf(r, parent, key, name, body, isEmptyBody(body));
    }

    /** Records a player stats table. It needs a header row and at least one player. */
    private void putTable(Rec r, JSONObject parent, String key, String name, String table) {
        String t = table == null ? "" : table.trim();
        int rows = t.isEmpty() ? 0 : t.split("\n").length;
        putLeaf(r, parent, key, name, t, rows < 2);
    }

    /** Records a tab that is not in the page's tab row. This never makes a match incomplete. */
    private void putMissing(Rec r, JSONObject parent, String key, String name) {
        r.missing.add(name);
        jput(parent, key, leaf("missing", ""));
    }

    /**
     * Cleans the visible text of a match page. Drops the odds and bonus block, ads, "show more"
     * buttons, video lines, the match momentum axis, the news list and everything after it
     * (footer). The tab row is always dropped. With withHeader the match header (teams,
     * score, status, round) is kept; without it the text starts where the tab content starts.
     */
    private static String cleanPage(String raw, boolean withHeader) {
        List<String> lines = new ArrayList<>();
        for (String s : (raw == null ? "" : raw).split("\n")) {
            String t = s.trim();
            if (!t.isEmpty()) lines.add(t);
        }
        int end = lines.size();
        for (int i = 0; i < lines.size(); i++) {
            String t = lines.get(i);
            if (t.equals("FLASHSCORE NEWS")
                    || (t.startsWith("Follow ") && t.contains("football coverage"))) {
                end = i;
                break;
            }
        }
        // The tab row starts at the first nav label (MATCH, or SUMMARY on small matches).
        int navStart = -1;
        for (int i = 0; i < Math.min(end, 80); i++) {
            if (indexOf(NAV_LABELS, lines.get(i)) >= 0) {
                navStart = i;
                break;
            }
        }
        int bodyStart = 0;
        if (navStart >= 0) {
            boolean[] used = new boolean[NAV_LABELS.length];
            int i = navStart;
            while (i < end) {
                int k = indexOf(NAV_LABELS, lines.get(i));
                if (k < 0 || used[k]) break;
                used[k] = true;
                i++;
            }
            bodyStart = i;
        }

        StringBuilder sb = new StringBuilder();
        boolean skipOdds = false;
        for (int i = withHeader ? 0 : bodyStart; i < end; i++) {
            if (withHeader && navStart >= 0 && i >= navStart && i < bodyStart) continue;
            String t = lines.get(i);
            String up = t.toUpperCase(Locale.ROOT);
            if (skipOdds) {
                if (isHeading(t) && indexOf(ODDS_LABELS, up) < 0) {
                    skipOdds = false;
                } else {
                    continue;
                }
            }
            if (up.equals("ODDS") && i + 1 < end
                    && indexOf(ODDS_LABELS, lines.get(i + 1).toUpperCase(Locale.ROOT)) >= 0) {
                skipOdds = true;
                continue;
            }
            if (indexOf(NOISE_LINES, up) >= 0) continue;
            if (up.equals("MATCH MOMENTUM")) {
                while (i + 1 < end && lines.get(i + 1).matches("\\d+'")) i++;
                continue;
            }
            sb.append(t).append('\n');
        }
        return sb.toString().trim();
    }

    /** True when the text has no data: nothing, or only sub-tab labels and "no data" lines. */
    private static boolean isEmptyBody(String body) {
        if (body == null) return true;
        for (String line : body.split("\n")) {
            String t = line.trim();
            if (t.isEmpty()) continue;
            if (indexOf(SUB_LABELS, t.toUpperCase(Locale.ROOT)) >= 0) continue;
            if (NO_DATA.matcher(t).find()) continue;
            return false;
        }
        return true;
    }

    private static boolean isHeading(String t) {
        return t.length() <= 40 && t.equals(t.toUpperCase(Locale.ROOT))
                && t.replaceAll("[^A-Za-z]", "").length() >= 4;
    }

    private static int indexOf(String[] arr, String s) {
        for (int i = 0; i < arr.length; i++) {
            if (arr[i].equals(s)) return i;
        }
        return -1;
    }

    /** Sub-tab labels from the page, without the main tabs and the team filter. */
    private static List<String> subTabLabels(String json) {
        List<String> out = new ArrayList<>();
        JSONArray arr = parseOrEmpty(json).optJSONArray("labels");
        if (arr == null) return out;
        for (int i = 0; i < arr.length(); i++) {
            String s = arr.optString(i).trim();
            if (s.isEmpty()) continue;
            if (indexOf(MAIN_TABS, s.toUpperCase(Locale.ROOT)) < 0) out.add(s);
        }
        return out;
    }

    private static String keyOf(String label) {
        return label.toLowerCase(Locale.ROOT).replaceAll("[^a-z0-9]+", "_").replaceAll("^_+|_+$", "");
    }

    private static String titleCase(String s) {
        String t = s.toLowerCase(Locale.ROOT);
        return t.isEmpty() ? t : Character.toUpperCase(t.charAt(0)) + t.substring(1);
    }

    // ---------------------------------------------------------------- helpers

    private static String clickTab(String txt) {
        return CLICK_TAB_JS.replace("__TXT__", txt);
    }

    private static String clickText(String txt) {
        return CLICK_TEXT_JS.replace("__TXT__", txt);
    }

    private static String midOf(String href) {
        if (href == null) return "";
        Matcher m = Pattern.compile("[?&]mid=([A-Za-z0-9]+)").matcher(href);
        return m.find() ? m.group(1) : "";
    }

    private static JSONObject parseOrEmpty(String json) {
        try {
            return new JSONObject(json);
        } catch (Exception e) {
            return new JSONObject();
        }
    }

    private static String unquote(String v) {
        if (v == null || v.equals("null")) return "";
        try {
            Object o = new JSONTokener(v).nextValue();
            return o == null ? "" : String.valueOf(o);
        } catch (JSONException e) {
            return v;
        }
    }

    private static void jput(JSONObject o, String k, Object v) {
        try {
            o.put(k, v);
        } catch (JSONException ignored) {
            // nothing to do
        }
    }

    private static JSONArray toArray(List<String> list) {
        JSONArray a = new JSONArray();
        for (String s : list) a.put(s);
        return a;
    }

    private static String join(List<String> list) {
        return join(list, ", ");
    }

    private static String join(List<String> list, String sep) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < list.size(); i++) {
            if (i > 0) sb.append(sep);
            sb.append(list.get(i));
        }
        return sb.toString();
    }

    private static String shorten(String s) {
        return shorten(s, 60);
    }

    private static String shorten(String s, int max) {
        if (s == null) return "";
        return s.length() > max ? s.substring(0, max) + "..." : s;
    }

    /** Only used on Android 9 and older, where Downloads is not reachable. */
    private void save(String name, String body) {
        try {
            File dir = getExternalFilesDir(null);
            if (dir == null) dir = getFilesDir();
            FileOutputStream fos = new FileOutputStream(new File(dir, name));
            fos.write(body.getBytes(StandardCharsets.UTF_8));
            fos.close();
        } catch (Exception e) {
            log("Could not save " + name + ": " + e);
        }
    }

    private void log(String line) {
        synchronized (logBuf) {
            logBuf.append(line).append('\n');
        }
        ui.post(() -> {
            synchronized (logBuf) {
                logView.setText(logBuf.toString());
            }
            scroll.post(() -> scroll.fullScroll(ScrollView.FOCUS_DOWN));
        });
    }
}
