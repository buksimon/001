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
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
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
 * Test app v1.2: Flashscore walker.
 *
 * Scrap, from a Flashscore match link with ?mid=:
 *  1. Main match: answer the consent box and the age check, wait until the page is really loaded
 *     (the tab row is on screen), then save SUMMARY, STATS (match, 1st half, 2nd half),
 *     LINEUPS, PLAYER STATS (every sub-tab), COMMENTARY and REPORT.
 *  2. H2H tab: "Show more matches" is clicked every time (and again while a team has fewer than
 *     10 league matches). Then the 10 latest LEAGUE matches of each team (the league is the
 *     competition code most of its latest matches carry, so friendlies, cups and European games
 *     are left out) and the 2 latest head-to-head matches are taken. The main match is never
 *     taken from those lists. A match in more than one list is opened once.
 *  3. Each of those matches gets the same capture as step 1.
 *  4. A page that does not load is loaded again. After a tab is clicked its data must really be
 *     on screen before it is read; a click that did not open the tab is repeated.
 *  5. After one round, the app goes back to each played match that has an empty tab and reads
 *     only what is still missing (up to 2 extra rounds; stops early when nothing new comes).
 *  6. A tab not in the tab row is "missing". A tab that came back blank is "empty". A tab where
 *     the page says there is no data is listed as empty but is not a failure. A match is
 *     complete when no tab came back blank and its summary was captured (a match not played
 *     yet: when its summary was captured).
 *
 * Needs no assets. For the notification on Android 13+, AndroidManifest.xml needs
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

  /** Matches to walk: the latest league matches of each team and the head-to-head matches. */
  private static final int H2H_COUNT = 2;
  private static final int LAST_COUNT = 10;
  private static final int TARGET_TOTAL = H2H_COUNT + 2 * LAST_COUNT;

  /** How many of a team's latest matches are looked at to find its league. */
  private static final int LEAGUE_WINDOW = 12;
  /** Most "Show more matches" rounds, and most extra passes over pages with empty tabs. */
  private static final int MAX_MORE_ROUNDS = 8;
  private static final int MAX_RETRY_PASSES = 2;

  /** A list row starts with the date, then the competition code: "27.09.26 L2 Alianza ...". */
  private static final Pattern ROW_CODE = Pattern.compile("^\\d{2}\\.\\d{2}\\.\\d{2}\\s+(\\S+)\\s");

  /** Competition codes that are never a team's league. Only used to break a tie. */
  private static final Set<String> NOT_LEAGUE = new HashSet<>(java.util.Arrays.asList(
      "FRI", "FRIENDLY", "CUP", "UCL", "UEL", "UECL", "ECL", "CL", "EL"));

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
   * stops changing), whether the match tab row is really on screen (two or more tabs: the page
   * has loaded, not just its text skeleton), and whether the age check is up.
   */
  private static final String READY_JS =
      "(function(){try{"
     + "var s=document.body?document.body.innerText:'';"
     + "var h=0;for(var i=0;i<s.length;i++){h=((h<<5)-h+s.charCodeAt(i))|0;}"
     + "var u=s.toUpperCase();"
     + "var tc=0;var tt=document.querySelectorAll('[data-testid=\"wcl-tab\"]');"
     + "for(var k=0;k<tt.length;k++){if(tt[k].offsetParent!==null)tc++;}"
     + "return JSON.stringify({h:h,n:s.length,tabs:(tc>=2),tc:tc,age:(u.indexOf('LEGAL AGE')>=0)});"
     + "}catch(err){return JSON.stringify({h:0,n:0,tabs:false,tc:0,age:false});}})()";

  /**
   * Answers a cookie / consent box if one is on screen. "Do not consent" style buttons are
   * tried first; only if the box has none, the "Consent / Accept" button. Returns "rejected",
   * "accepted" or "none".
   */
  private static final String CONSENT_JS =
      "(function(){try{"
     + "function vis(e){return e&&e.offsetParent!==null;}"
     + "function norm(e){return (e.innerText||e.value||'').replace(/\\s+/g,' ').trim().toLowerCase();}"
     + "var rej=['#onetrust-reject-all-handler','.fc-cta-do-not-consent','#didomi-notice-disagree-button'];"
     + "var acc=['#onetrust-accept-btn-handler','.fc-cta-consent','#didomi-notice-agree-button'];"
     + "var rejRe=/^(do not consent|reject all|reject|refuse all|refuse|disagree|decline|deny all|deny)$/;"
     + "var accRe=/^(consent|i accept|accept all|accept|agree|agree and close|allow all|got it)$/;"
     + "var btn=document.querySelectorAll('button,a,[role=button],input[type=button]');"
     + "var i,e;"
     + "for(i=0;i<rej.length;i++){e=document.querySelector(rej[i]);if(vis(e)){e.click();return 'rejected';}}"
     + "for(i=0;i<btn.length;i++){if(vis(btn[i])&&rejRe.test(norm(btn[i]))){btn[i].click();return 'rejected';}}"
     + "for(i=0;i<acc.length;i++){e=document.querySelector(acc[i]);if(vis(e)){e.click();return 'accepted';}}"
     + "var box=document.body?document.body.innerText.toLowerCase():'';"
     + "if(box.indexOf('we and our partners')>=0||box.indexOf('your privacy choices')>=0||box.indexOf('we value your privacy')>=0){"
     + "for(i=0;i<btn.length;i++){if(vis(btn[i])&&accRe.test(norm(btn[i]))){btn[i].click();return 'accepted';}}}"
     + "return 'none';"
     + "}catch(err){return 'none';}})()";

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

  /**
   * Clicks every visible "Show more matches" button (the innermost element that has that text,
   * so one button is clicked once). Returns how many it clicked.
   */
  private static final String SHOW_MORE_JS =
      "(function(){"
     + "function norm(x){return (x||'').replace(/\\s+/g,' ').trim().toLowerCase().replace(/[^a-z ]/g,'').trim();}"
     + "var c=document.querySelectorAll('a,button,span,div');var n=0;"
     + "for(var i=0;i<c.length;i++){var e=c[i];"
     + "if(e.offsetParent===null)continue;"
     + "if(norm(e.innerText)!=='show more matches')continue;"
     + "if(e.getElementsByTagName('*').length>=6)continue;"
     + "var inner=false;"
     + "for(var k=0;k<e.children.length;k++){if(norm(e.children[k].innerText)==='show more matches'){inner=true;break;}}"
     + "if(inner)continue;"
     + "e.scrollIntoView();e.click();n++;}"
     + "return String(n);})()";

  /** The visible tabs of the page (the tab row and the sub-tab rows), lower case. */
  private static final String TABS_JS =
      "(function(){var o=[];try{"
     + "var tabs=document.querySelectorAll('[data-testid=\"wcl-tab\"]');"
     + "for(var i=0;i<tabs.length;i++){var e=tabs[i];if(e.offsetParent===null)continue;"
     + "o.push((e.innerText||'').trim().replace(/\\s+/g,' ').toLowerCase());}"
     + "}catch(err){}return JSON.stringify(o);})()";

  /**
   * The page text (t) and the tabs that show as selected (s, lower case). If the page does not
   * mark the selected tab, s is empty and the walker goes by the text changing instead.
   */
  private static final String SNAP_SEL_JS =
      "(function(){try{var s=[];"
     + "var tabs=document.querySelectorAll('[data-testid=\"wcl-tab\"]');"
     + "for(var i=0;i<tabs.length;i++){var e=tabs[i];"
     + "var a=e.getAttribute('aria-selected');"
     + "var sel=(a==='true')||(e.getAttribute('aria-current')==='true')||(e.getAttribute('data-selected')==='true')"
     + "||(a===null&&/selected/i.test(String(e.className||'')));"
     + "if(sel)s.push((e.innerText||'').trim().replace(/\\s+/g,' ').toLowerCase());}"
     + "return JSON.stringify({t:(document.body?document.body.innerText:''),s:s});"
     + "}catch(err){return JSON.stringify({t:'',s:[]});}})()";

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
  private boolean loadFailed = false;
  private int retryPass = 0;
  private int capturedBefore = -1;
  private String homeLeague = "";
  private String awayLeague = "";

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
    /** Each tab by name: captured, empty (came back blank), nodata (the page says none) or missing. */
    final Map<String, String> state = new LinkedHashMap<>();
    final List<String> tabRow = new ArrayList<>();   // the tabs the page shows, lower case
    boolean played = true;     // false only for a main match that has not been played yet
    boolean retry = false;     // true once the app has gone back to this page
    boolean counted = false;
    int passes = 1;
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

  private interface Flag {
    void run(boolean ok);
  }

  /** Result of reading a tab: found is false when the tab is not on the page. */
  private interface TabCb {
    void run(boolean found, String raw);
  }

  private interface Labels {
    void run(List<String> labels, boolean noData);
  }

  private interface Grown {
    void run(JSONObject o, boolean grew);
  }

  /** The state of one "click a tab and wait for its data". */
  private static class TabPoll {
    String txt = "";
    int before;
    int maxTries = 40;
    boolean requireChange;
    boolean changed;
    int tries;
    int stable;
    int lastHash = -1;
    int clicks = 1;
  }

  // ---------------------------------------------------------------- screen

  @Override
  protected void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);
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
      public void onReceivedError(WebView view, WebResourceRequest request,
                    WebResourceError error) {
        super.onReceivedError(view, request, error);
        if (walking && onLoaded != null && request != null && request.isForMainFrame()) {
          loadFailed = true;
          final int token = loadToken;
          final String failed = request.getUrl().toString();
          log("   the page gave an error, loading it again in 4 s");
          ui.postDelayed(() -> {
            if (walking && token == loadToken && onLoaded != null) {
              loadFailed = false;
              webView.loadUrl(failed);
            }
          }, 4000);
        }
      }

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
        if (walking && onLoaded != null && !loadFailed) {
          final Runnable r = onLoaded;
          onLoaded = null;
          ui.postDelayed(() -> {
            if (walking) r.run();
          }, 2500);
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
      if (!tabsShown) webView.evaluateJavascript(CONSENT_JS, null);
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
    retryPass = 0;
    capturedBefore = -1;
    homeLeague = "";
    awayLeague = "";
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

  // ---- loading a page

  /**
   * Loads a page and runs next once it has loaded. A page that does not load (no signal, an
   * error, a hang) is loaded again and again until it does, or until Stop is tapped.
   */
  private void loadThen(final String url, final Runnable next) {
    if (!walking) return;
    final int token = ++loadToken;
    onLoaded = next;
    loadFailed = false;
    loadAttempt(url, token, 0);
  }

  private void loadAttempt(final String url, final int token, final int attempt) {
    if (!walking || token != loadToken || onLoaded == null) return;
    if (attempt > 0) log("   the page did not load, loading it again (try " + (attempt + 1) + ")");
    loadFailed = false;
    webView.loadUrl(url);
    ui.postDelayed(() -> {
      if (!walking || token != loadToken || onLoaded == null) return;
      // 45 s and the page never said it had finished. If it is on screen, go on; if not, load again.
      jsWalk(READY_JS, json -> {
        if (token != loadToken || onLoaded == null) return;
        JSONObject o = parseOrEmpty(json);
        if (o.optBoolean("tabs") && o.optInt("n") > 150) {
          Runnable r = onLoaded;
          onLoaded = null;
          log("   (the page is on screen, going on)");
          r.run();
        } else {
          loadAttempt(url, token, attempt + 1);
        }
      });
    }, 45000);
  }

  private void jsWalk(String script, Cb cb) {
    if (!walking) return;
    webView.evaluateJavascript(script, v -> {
      if (walking) cb.run(unquote(v));
    });
  }

  // ---- waiting for a page

  /**
   * Waits until the page is really there: the match tabs are on screen and the text has not
   * changed for 2 seconds. Answers the age check YES. ok is false if that did not happen in 20 s.
   */
  private void waitPageReady(final String label, final Flag done) {
    pageReady(0, -1, 0, label, 40, done);
  }

  private void pageReady(final int tries, final int lastHash, final int stable,
              final String label, final int maxTries, final Flag done) {
    if (!walking) return;
    jsWalk(READY_JS, json -> {
      final JSONObject o = parseOrEmpty(json);
      final int h = o.optInt("h");
      final int n = o.optInt("n");
      final boolean tabsShown = o.optBoolean("tabs");
      if (!tabsShown || tries % 8 == 0) {
        // a consent box can cover the page and keep it from loading: answer it
        jsWalk(CONSENT_JS, c -> {
          if ("rejected".equals(c) || "accepted".equals(c)) log("Consent box on screen: " + c);
        });
      }
      if (o.optBoolean("age")) {
        log("Age check on screen: answering YES");
        tryClick("yes", 0, 3, false, res -> {
          ui.postDelayed(() -> pageReady(tries + 1, -1, 0, label, maxTries, done), 800);
        });
        return;
      }
      final int nextStable = (tabsShown && n > 150 && h == lastHash) ? stable + 1 : 0;
      if (nextStable >= 4) {
        if (label != null) status("Page ready ✓ " + label);
        done.run(true);
        return;
      }
      if (tries >= maxTries) {
        done.run(false);
        return;
      }
      ui.postDelayed(() -> pageReady(tries + 1, h, nextStable, label, maxTries, done), 500);
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

  /** The tabs in the page's tab row, read once the page is ready. */
  private void readTabRow(final Rec r, final Runnable next) {
    jsWalk(TABS_JS, json -> {
      r.tabRow.clear();
      try {
        JSONArray a = new JSONArray(json);
        for (int i = 0; i < a.length(); i++) r.tabRow.add(a.optString(i));
      } catch (JSONException ignored) {
        // no tab row read: every tab is looked for the long way
      }
      next.run();
    });
  }

  /** How long to look for a tab: long if it is in the tab row, a moment if it is not. */
  private static int findTries(Rec r, String tab) {
    return (r.tabRow.isEmpty() || r.tabRow.contains(tab)) ? 4 : 2;
  }

  // ---- reading a tab after it is clicked

  /**
   * Clicks a tab and waits until its data is really on screen: the page has changed since the
   * click (or the tab shows as selected) and the text has stopped changing for 1.5 s. A tab
   * that shows "no data" is accepted after 4 s. The click is repeated if the tab did not open.
   * Calls done(false, "") when the tab is not on the page.
   */
  private void readTab(final String txt, final int findTries, final int maxTries,
             final boolean requireChange, final TabCb done) {
    jsWalk(SNAP_SEL_JS, json -> {
      final TabPoll p = new TabPoll();
      p.txt = txt;
      p.maxTries = maxTries;
      p.requireChange = requireChange;
      p.before = cleanPage(parseOrEmpty(json).optString("t"), false).hashCode();
      waitClick(txt, findTries, res -> {
        if (!"ok".equals(res)) {
          done.run(false, "");
          return;
        }
        pollTab(p, done);
      });
    });
  }

  private void pollTab(final TabPoll p, final TabCb done) {
    ui.postDelayed(() -> jsWalk(SNAP_SEL_JS, json -> {
      JSONObject o = parseOrEmpty(json);
      String raw = o.optString("t");
      JSONArray sel = o.optJSONArray("s");
      p.tries++;
      String body = cleanPage(raw, false);
      int h = body.hashCode();
      if (h != p.before) p.changed = true;
      boolean selected = false;
      if (sel != null) {
        for (int i = 0; i < sel.length(); i++) {
          if (p.txt.equals(sel.optString(i))) selected = true;
        }
      }
      boolean open = !p.requireChange || p.changed || (selected && p.tries >= 8);
      if (open) {
        if (h == p.lastHash) p.stable++;
        else p.stable = 0;
        p.lastHash = h;
        boolean empty = isEmptyBody(body);
        if (!empty && p.stable >= 3) {
          done.run(true, raw);
          return;
        }
        if (empty && hasNoDataLine(body) && p.stable >= 8) {
          done.run(true, raw);
          return;
        }
      } else if (p.tries % 8 == 0 && p.clicks < 3) {
        p.clicks++;
        log("   the tab did not open, clicking it again");
        jsWalk(clickTab(p.txt), res -> { });
      }
      if (p.tries >= p.maxTries) {
        done.run(true, open ? raw : "");
        return;
      }
      pollTab(p, done);
    }), 500);
  }

  /** Same for a tab whose data is a table (player stats). txt null: just wait for the table. */
  private void readTable(final String txt, final int findTries, final boolean requireChange,
              final TabCb done) {
    jsWalk(TABLE_JS, before -> {
      final int h0 = before.hashCode();
      if (txt == null) {
        pollTable(h0, requireChange, 0, -1, 0, done);
        return;
      }
      waitClick(txt, findTries, res -> {
        if (!"ok".equals(res)) {
          done.run(false, "");
          return;
        }
        pollTable(h0, requireChange, 0, -1, 0, done);
      });
    });
  }

  private void pollTable(final int before, final boolean requireChange, final int tries,
              final int lastHash, final int stable, final TabCb done) {
    ui.postDelayed(() -> jsWalk(TABLE_JS, table -> {
      int h = table.hashCode();
      boolean changed = !requireChange || h != before;
      int st = (h == lastHash) ? stable + 1 : 0;
      String t = table.trim();
      int rows = t.isEmpty() ? 0 : t.split("\n").length;
      if (changed && rows >= 2 && st >= 3) {
        done.run(true, table);
        return;
      }
      if (tries + 1 >= 30) {
        done.run(true, changed ? table : "");
        return;
      }
      pollTable(before, requireChange, tries + 1, h, st, done);
    }), 500);
  }

  // ---- step 1 and 3: capture one match page

  /**
   * Captures SUMMARY, STATS, LINEUPS, PLAYER STATS, COMMENTARY and REPORT on the page that is
   * loading. Waits for the page before it starts; a page that never shows up is loaded again.
   * On a second pass (r.retry) only what is not captured yet is read again.
   */
  private void captureRecord(final Rec r, final String label, final Runnable done) {
    showPage("Waiting for the page", 0, 1);
    waitPageReady(label, ok -> {
      if (!ok) {
        log("   the page is not ready, loading it again");
        loadThen(r.url, () -> captureRecord(r, label, done));
        return;
      }
      readTabRow(r, () -> readSummary(r, 0, () -> stepStats(r, () -> stepLineups(r,
          () -> stepPlayerStats(r, () -> stepCommentary(r, () -> stepReport(r, done)))))));
    });
  }

  /** SUMMARY: the page as it opens. If it comes back empty the page is still filling: look again. */
  private void readSummary(final Rec r, final int tries, final Runnable next) {
    if (r.retry && "captured".equals(r.state.get("Summary"))) {
      next.run();
      return;
    }
    showPage("Summary", 0, 1);
    jsWalk(SNAP_JS, raw -> {
      boolean empty = isEmptyBody(cleanPage(raw, false));
      if (empty && tries < 20) {
        ui.postDelayed(() -> readSummary(r, tries + 1, next), 500);
        return;
      }
      String header = cleanPage(raw, true);
      r.played = r != mainRec || looksPlayed(header);
      putLeaf(r, r.tabs, "summary", "Summary", header, empty);
      showPage("Summary", 1, 1);
      next.run();
    });
  }

  /** STATS: the MATCH view, then 1ST HALF and 2ND HALF. */
  private void stepStats(final Rec r, final Runnable next) {
    if (stepDone(r, "Stats")) {
      next.run();
      return;
    }
    showPage("Stats", 0, 3);
    readTab("stats", findTries(r, "stats"), 40, true, (found, raw) -> {
      if (!found) {
        putMissing(r, r.tabs, "stats", "Stats");
        next.run();
        return;
      }
      final JSONObject stats = objectFor(r, r.tabs, "stats", "Stats");
      putBody(r, stats, "match", "Stats / match", raw);
      showPage("Stats", 1, 3);
      // no data on the MATCH view: the half tabs are not there either, so do not wait for them
      final boolean quick = !"captured".equals(r.state.get("Stats / match"));
      statSub(r, stats, "1st half", "first_half", "Stats / 1st half", 2, quick,
          () -> statSub(r, stats, "2nd half", "second_half", "Stats / 2nd half", 3, quick, next));
    });
  }

  private void statSub(final Rec r, final JSONObject parent, final String clickLabel,
             final String key, final String name, final int step,
             final boolean quick, final Runnable next) {
    readTab(clickLabel, quick ? 1 : 4, 40, true, (found, raw) -> {
      if (!found) {
        putMissing(r, parent, key, name);
      } else {
        putBody(r, parent, key, name, raw);
      }
      showPage("Stats", step, 3);
      next.run();
    });
  }

  /**
   * LINEUPS: on a finished match the ratings are already in the page. AVG. RATING is clicked
   * once if it is there.
   */
  private void stepLineups(final Rec r, final Runnable next) {
    if (stepDone(r, "Lineups")) {
      next.run();
      return;
    }
    showPage("Lineups", 0, 1);
    readTab("lineups", findTries(r, "lineups"), 40, true, (found, raw) -> {
      if (!found) {
        putMissing(r, r.tabs, "lineups", "Lineups");
        next.run();
        return;
      }
      if (isEmptyBody(cleanPage(raw, false))) {
        putBody(r, r.tabs, "lineups", "Lineups", raw);
        showPage("Lineups", 1, 1);
        next.run();
        return;
      }
      readTab("avg. rating", 1, 10, true, (ok, raw2) -> {
        String use = (ok && !isEmptyBody(cleanPage(raw2, false))) ? raw2 : raw;
        putBody(r, r.tabs, "lineups", "Lineups", use);
        showPage("Lineups", 1, 1);
        next.run();
      });
    });
  }

  /** PLAYER STATS: every sub-tab the page shows, one line per player. */
  private void stepPlayerStats(final Rec r, final Runnable next) {
    if (stepDone(r, "Player stats")) {
      next.run();
      return;
    }
    showPage("Player stats", 0, 1);
    waitClick("player stats", findTries(r, "player stats"), res -> {
      if (!"ok".equals(res)) {
        putMissing(r, r.tabs, "player_stats", "Player stats");
        next.run();
        return;
      }
      final JSONObject ps = objectFor(r, r.tabs, "player_stats", "Player stats");
      waitSubTabs(0, (labels, noData) -> {
        if (labels.isEmpty()) {
          if (noData) {
            putNoData(r, ps, "default", "Player stats");
            showPage("Player stats", 1, 1);
            next.run();
            return;
          }
          readTable(null, 0, false, (f, table) -> {
            putTable(r, ps, "default", "Player stats", table);
            showPage("Player stats", 1, 1);
            next.run();
          });
          return;
        }
        log("   player stats sub-tabs: " + labels);
        // an earlier pass that found no sub-tabs kept one plain table: the sub-tabs replace it
        ps.remove("default");
        r.state.remove("Player stats");
        subTabs(r, ps, labels, 0, next);
      });
    });
  }

  /** Waits for the sub-tab row of PLAYER STATS to appear (up to 14 s, or until the page says no data). */
  private void waitSubTabs(final int tries, final Labels done) {
    jsWalk(PLAYER_SUBTABS_JS, json -> {
      final List<String> labels = subTabLabels(json);
      if (!labels.isEmpty() || tries >= 20) {
        done.run(labels, false);
        return;
      }
      if (tries == 10) jsWalk(clickTab("player stats"), res -> { });
      if (tries >= 6) {
        jsWalk(SNAP_JS, raw -> {
          if (hasNoDataLine(cleanPage(raw, false))) {
            done.run(labels, true);
          } else {
            ui.postDelayed(() -> waitSubTabs(tries + 1, done), 700);
          }
        });
        return;
      }
      ui.postDelayed(() -> waitSubTabs(tries + 1, done), 700);
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
    // the first sub-tab (TOP STATS) is already open, so its table does not have to change
    final boolean first = i == 0 || label.equalsIgnoreCase("TOP STATS");
    readTable(label.toLowerCase(Locale.ROOT), 4, !first, (found, table) -> {
      if (!found) {
        putMissing(r, ps, key, "Player stats / " + titleCase(label));
      } else {
        putTable(r, ps, key, "Player stats / " + titleCase(label), table);
      }
      showPage(shown, i + 1, labels.size());
      subTabs(r, ps, labels, i + 1, next);
    });
  }

  /** COMMENTARY: the text of the tab as shown. */
  private void stepCommentary(final Rec r, final Runnable next) {
    stepText(r, "commentary", "commentary", "Commentary", next);
  }

  /** REPORT: the article page. */
  private void stepReport(final Rec r, final Runnable next) {
    stepText(r, "report", "report", "Report", next);
  }

  private void stepText(final Rec r, final String tab, final String key, final String name,
             final Runnable next) {
    if (stepDone(r, name)) {
      next.run();
      return;
    }
    showPage(name, 0, 1);
    readTab(tab, findTries(r, tab), 40, true, (found, raw) -> {
      if (!found) {
        putMissing(r, r.tabs, key, name);
      } else {
        putBody(r, r.tabs, key, name, raw);
      }
      showPage(name, 1, 1);
      next.run();
    });
  }

  /** On a second pass: true when this tab (and its sub-tabs) was captured on an earlier pass. */
  private static boolean stepDone(Rec r, String prefix) {
    if (!r.retry) return false;
    boolean any = false;
    for (Map.Entry<String, String> e : r.state.entrySet()) {
      String k = e.getKey();
      if (k.equals(prefix) || k.startsWith(prefix + " / ")) {
        any = true;
        if (!"captured".equals(e.getValue()) && !"nodata".equals(e.getValue())) return false;
      }
    }
    return any;
  }

  /** The object a tab with sub-tabs is kept in. An object from an earlier pass is reused. */
  private JSONObject objectFor(Rec r, JSONObject parent, String key, String name) {
    JSONObject cur = parent.optJSONObject(key);
    if (cur != null && !cur.has("status")) return cur;
    JSONObject fresh = new JSONObject();
    jput(parent, key, fresh);
    r.state.remove(name);
    return fresh;
  }

  private void finishRecord(Rec r) {
    r.done = true;
    rebuildLists(r);
    // A match that has not been played has no stats, so empty tabs are expected there.
    r.complete = r.summaryOk && (!r.emptyFound || !r.played);
    log((r == mainRec ? "Main match" : "Match") + ": " + (r.complete ? "complete" : "incomplete")
        + (r.played ? "" : "  (not played yet, so empty tabs are normal)")
        + (r.missing.isEmpty() ? "" : "  (not on page: " + join(r.missing) + ")")
        + (r.emptyTabs.isEmpty() ? "" : "  (empty: " + join(r.emptyTabs) + ")"));
    if (r != mainRec && !r.counted) {
      r.counted = true;
      doneSlots += r.groups.size();
      updateCounter();
    }
  }

  /** Rebuilds the missing / empty lists from what each tab ended up as. */
  private static void rebuildLists(Rec r) {
    r.missing.clear();
    r.emptyTabs.clear();
    boolean failed = false;
    for (Map.Entry<String, String> e : r.state.entrySet()) {
      String v = e.getValue();
      if ("missing".equals(v)) {
        r.missing.add(e.getKey());
      } else if ("empty".equals(v)) {
        r.emptyTabs.add(e.getKey());
        failed = true;
      } else if ("nodata".equals(v)) {
        r.emptyTabs.add(e.getKey());   // the page itself says there is no data: not a failure
      }
    }
    r.emptyFound = failed;
    r.summaryOk = "captured".equals(r.state.get("Summary"));
  }

  private static boolean looksPlayed(String header) {
    String u = header.toUpperCase(Locale.ROOT);
    return u.contains("FINISHED") || u.contains("AFTER EXTRA TIME") || u.contains("AFTER PENALTIES")
        || u.contains("AWARDED") || u.contains("WALKOVER");
  }

  // ---- step 1: the main match, then the H2H tab

  private void walkMain() {
    matchLabel.setText("Main match");
    captureRecord(mainRec, "main match", () -> {
      finishRecord(mainRec);
      stepH2H(0);
    });
  }

  private void stepH2H(final int attempt) {
    status("Opening the H2H tab...");
    matchLabel.setText("Main match");
    showPage("H2H", 0, 1);
    waitClick("h2h", 20, res -> {
      if (!"ok".equals(res)) {
        if (attempt < 2) {
          status("H2H tab not found. Loading the main page again...");
          loadThen(matchUrl, () -> waitPageReady("main match", ok -> stepH2H(attempt + 1)));
          return;
        }
        status("H2H tab not found. Only the main match was saved.");
        pageNotes.add("H2H tab not found on the main match page.");
        finishWalk(true);
        return;
      }
      waitPageReady(null, ok -> waitClick("overall", 3, o ->
          waitPageReady(null, ok2 -> pollH2H(0, attempt))));
    });
  }

  /**
   * Waits for the H2H sections to render (up to 35 s). If they do not, the tab is clicked
   * again, and if they still do not the main page is loaded again (twice at most).
   */
  private void pollH2H(final int tries, final int attempt) {
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
      if (h2h && lastCount >= 2) {
        showMore(o, 0);
        return;
      }
      if (tries == 12 || tries == 24) {
        log("   the H2H lists are not there yet, opening the tab again");
        jsWalk(clickTab("h2h"), res -> { });
      }
      if (tries < 35) {
        ui.postDelayed(() -> pollH2H(tries + 1, attempt), 1000);
        return;
      }
      if (attempt < 2) {
        status("H2H did not load. Loading the main page again...");
        loadThen(matchUrl, () -> waitPageReady("main match", ok -> stepH2H(attempt + 1)));
        return;
      }
      pageNotes.add("The H2H lists did not load.");
      showMore(o, 0);
    });
  }

  /**
   * Clicks "Show more matches" every time, at least once, and again while a team still has
   * fewer than LAST_COUNT league matches (or H2H fewer than H2H_COUNT) to take.
   */
  private void showMore(final JSONObject o, final int round) {
    if (!walking) return;
    if ((round > 0 && !isShort(o)) || round >= MAX_MORE_ROUNDS) {
      processSections(o);
      return;
    }
    final int before = rowTotal(o);
    showPage("Show more matches", round, MAX_MORE_ROUNDS);
    jsWalk(SHOW_MORE_JS, n -> {
      int clicked = 0;
      try {
        clicked = Integer.parseInt(n.trim());
      } catch (NumberFormatException ignored) {
        // treated as no button
      }
      if (clicked == 0) {
        log(round == 0 ? "No 'Show more matches' button on the page."
            : "No more 'Show more matches' buttons.");
        processSections(o);
        return;
      }
      log("Show more matches: clicked " + clicked + " button(s) (round " + (round + 1) + ").");
      waitRowsGrow(before, 0, -1, 0, (grown, grew) -> {
        if (grew) {
          showMore(grown, round + 1);
        } else {
          processSections(grown);
        }
      });
    });
  }

  /** After a click: waits until the lists have more rows and have stopped growing. */
  private void waitRowsGrow(final int before, final int tries, final int lastTotal,
               final int stable, final Grown done) {
    ui.postDelayed(() -> jsWalk(H2H_LIST_JS, json -> {
      JSONObject o = parseOrEmpty(json);
      int total = rowTotal(o);
      int st = (total == lastTotal) ? stable + 1 : 0;
      if (total > before && st >= 2) {
        done.run(o, true);
        return;
      }
      if (tries >= 14) {
        done.run(o, total > before);
        return;
      }
      waitRowsGrow(before, tries + 1, total, st, done);
    }), 700);
  }

  private static int rowTotal(JSONObject o) {
    int n = 0;
    JSONArray secs = o.optJSONArray("sections");
    if (secs == null) return 0;
    for (int i = 0; i < secs.length(); i++) {
      JSONObject s = secs.optJSONObject(i);
      JSONArray rows = s == null ? null : s.optJSONArray("rows");
      if (rows != null) n += rows.length();
    }
    return n;
  }

  /** What would be taken from the lists as they are now. */
  private static class Plan {
    JSONObject h2hSec;
    JSONObject homeSec;
    JSONObject awaySec;
    List<JSONObject> h2h = new ArrayList<>();
    List<JSONObject> home = new ArrayList<>();
    List<JSONObject> away = new ArrayList<>();
    String homeLeague = "";
    String awayLeague = "";
    int homeSkipped;
    int awaySkipped;
  }

  private Plan plan(JSONObject o) {
    Plan p = new Plan();
    JSONArray secs = o.optJSONArray("sections");
    List<JSONObject> lastSecs = new ArrayList<>();
    if (secs != null) {
      for (int i = 0; i < secs.length(); i++) {
        JSONObject s = secs.optJSONObject(i);
        if (s == null) continue;
        String type = s.optString("type");
        if ("h2h".equals(type) && p.h2hSec == null) {
          p.h2hSec = s;
        } else if ("last".equals(type)) {
          lastSecs.add(s);
        }
      }
    }
    p.homeSec = lastSecs.size() >= 1 ? lastSecs.get(0) : null;
    p.awaySec = lastSecs.size() >= 2 ? lastSecs.get(1) : null;
    int[] skipped = new int[1];
    p.h2h = pick(p.h2hSec, H2H_COUNT, "", skipped);
    p.homeLeague = leagueCode(p.homeSec);
    p.home = pick(p.homeSec, LAST_COUNT, p.homeLeague, skipped);
    p.homeSkipped = skipped[0];
    p.awayLeague = leagueCode(p.awaySec);
    p.away = pick(p.awaySec, LAST_COUNT, p.awayLeague, skipped);
    p.awaySkipped = skipped[0];
    return p;
  }

  private boolean isShort(JSONObject o) {
    Plan p = plan(o);
    return (p.h2hSec != null && p.h2h.size() < H2H_COUNT)
        || (p.homeSec != null && p.home.size() < LAST_COUNT)
        || (p.awaySec != null && p.away.size() < LAST_COUNT);
  }

  /**
   * The competition code of a row: "27.09.26 L2 Alianza Huanuco Tacna Heroica 2 2" gives "L2".
   * Empty when the row does not look like that.
   */
  private static String codeOf(String rowText) {
    Matcher m = ROW_CODE.matcher(rowText == null ? "" : rowText.trim());
    return m.find() ? m.group(1) : "";
  }

  /** True for a row that can be taken: it has a match link and is not the main match. */
  private boolean usable(JSONObject row) {
    if (row == null) return false;
    String id = midOf(row.optString("h"));
    return !row.optString("h").isEmpty() && !id.isEmpty() && !id.equals(mid);
  }

  /**
   * The league of a team's list: the competition code that most of its latest matches carry.
   * Friendlies, cups and European games are a few rows each, so the league wins. On a tie a
   * code that is not a known friendly/cup/European code wins, then the more recent match. Empty
   * when no code can be read (then nothing is filtered).
   */
  private String leagueCode(JSONObject sec) {
    if (sec == null) return "";
    JSONArray rows = sec.optJSONArray("rows");
    if (rows == null) return "";
    Map<String, Integer> count = new LinkedHashMap<>();
    Set<String> seen = new HashSet<>();
    int looked = 0;
    for (int i = 0; i < rows.length() && looked < LEAGUE_WINDOW; i++) {
      JSONObject row = rows.optJSONObject(i);
      if (!usable(row)) continue;
      if (!seen.add(midOf(row.optString("h")))) continue;
      looked++;
      String code = codeOf(row.optString("t"));
      if (code.isEmpty()) continue;
      Integer c = count.get(code);
      count.put(code, c == null ? 1 : c + 1);
    }
    String best = "";
    int bestN = 0;
    for (Map.Entry<String, Integer> e : count.entrySet()) {
      boolean better = e.getValue() > bestN
          || (e.getValue() == bestN && NOT_LEAGUE.contains(best) && !NOT_LEAGUE.contains(e.getKey()));
      if (better) {
        best = e.getKey();
        bestN = e.getValue();
      }
    }
    return best;
  }

  /**
   * The first max matches of a section, newest first, without the main match, without repeats
   * and, when a league code is given, only matches of that competition. skipped[0] is the
   * number of matches left out because they were another competition.
   */
  private List<JSONObject> pick(JSONObject sec, int max, String league, int[] skipped) {
    List<JSONObject> out = new ArrayList<>();
    skipped[0] = 0;
    if (sec == null) return out;
    JSONArray rows = sec.optJSONArray("rows");
    if (rows == null) return out;
    Set<String> seen = new HashSet<>();
    for (int i = 0; i < rows.length() && out.size() < max; i++) {
      JSONObject row = rows.optJSONObject(i);
      if (!usable(row)) continue;
      if (!seen.add(midOf(row.optString("h")))) continue;
      if (!league.isEmpty() && !league.equals(codeOf(row.optString("t")))) {
        skipped[0]++;
        continue;
      }
      out.add(row);
    }
    return out;
  }

  /** Builds the list of matches to open from what is on the page now. */
  private void processSections(JSONObject o) {
    if (!walking) return;
    Plan p = plan(o);
    Map<String, Rec> byMid = new LinkedHashMap<>();
    List<Rec> h2hSel = select(p.h2h, "h2h", byMid);
    List<Rec> homeSel = select(p.home, "home", byMid);
    List<Rec> awaySel = select(p.away, "away", byMid);

    if (p.homeSec != null) {
      String n = p.homeSec.optString("name").trim();
      homeName = n.isEmpty() ? "Home" : n;
    }
    if (p.awaySec != null) {
      String n = p.awaySec.optString("name").trim();
      awayName = n.isEmpty() ? "Away" : n;
    }
    homeLeague = p.homeLeague;
    awayLeague = p.awayLeague;
    if (p.homeSec != null) {
      log(homeName + ": league " + (homeLeague.isEmpty() ? "not known (no filter)" : homeLeague)
          + ", " + p.homeSkipped + " other-competition match(es) left out.");
    }
    if (p.awaySec != null) {
      log(awayName + ": league " + (awayLeague.isEmpty() ? "not known (no filter)" : awayLeague)
          + ", " + p.awaySkipped + " other-competition match(es) left out.");
    }
    if (p.h2hSec == null) pageNotes.add("HEAD-TO-HEAD MATCHES section not found.");
    if (p.homeSec == null) pageNotes.add("LAST MATCHES section for the home team not found.");
    if (p.awaySec == null) pageNotes.add("LAST MATCHES section for the away team not found.");
    if (p.h2hSec != null && h2hSel.size() < H2H_COUNT) {
      pageNotes.add("Only " + h2hSel.size() + " of " + H2H_COUNT + " head-to-head matches on the page.");
    }
    if (p.homeSec != null && homeSel.size() < LAST_COUNT) {
      pageNotes.add("Only " + homeSel.size() + " of " + LAST_COUNT + " league matches for " + homeName + ".");
    }
    if (p.awaySec != null && awaySel.size() < LAST_COUNT) {
      pageNotes.add("Only " + awaySel.size() + " of " + LAST_COUNT + " league matches for " + awayName + ".");
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

  /** One Rec per distinct match; a match in more than one list is the same Rec in each. */
  private List<Rec> select(List<JSONObject> rows, String group, Map<String, Rec> byMid) {
    List<Rec> out = new ArrayList<>();
    for (JSONObject row : rows) {
      String href = row.optString("h");
      String id = midOf(href);
      Rec r = byMid.get(id);
      if (r == null) {
        r = new Rec();
        r.mid = id;
        r.url = href;
        r.rowText = row.optString("t");
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
      startRetry();
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

  // ---- going back for what is missing

  /** True for a played match whose summary is not captured or that has a tab that came back empty. */
  private static boolean needsRetry(Rec r) {
    return r != null && r.played && (!r.done || !r.summaryOk || r.emptyFound);
  }

  private static int capturedIn(Rec r) {
    int n = 0;
    if (r == null) return 0;
    for (String v : r.state.values()) {
      if ("captured".equals(v)) n++;
    }
    return n;
  }

  private int capturedCount() {
    int n = capturedIn(mainRec);
    for (Rec r : recs) n += capturedIn(r);
    return n;
  }

  /**
   * After every match has been opened once: goes back to the ones with a tab that came back
   * empty (or a summary that did not load) and reads only what is still missing. Stops when
   * nothing is left, when a pass brought nothing new, or after MAX_RETRY_PASSES passes.
   */
  private void startRetry() {
    if (!walking) return;
    final List<Rec> todo = new ArrayList<>();
    if (needsRetry(mainRec)) todo.add(mainRec);
    for (Rec r : recs) {
      if (needsRetry(r)) todo.add(r);
    }
    int now = capturedCount();
    if (todo.isEmpty()) {
      finishWalk(true);
      return;
    }
    if (retryPass >= MAX_RETRY_PASSES || (capturedBefore >= 0 && now <= capturedBefore)) {
      log(todo.size() + " page(s) still have empty tabs after " + retryPass
          + " extra pass(es). Saving what was collected.");
      finishWalk(true);
      return;
    }
    capturedBefore = now;
    retryPass++;
    status("Going back to " + todo.size() + " page(s) with empty tabs (extra pass " + retryPass + ").");
    retryRec(todo, 0);
  }

  private void retryRec(final List<Rec> todo, final int i) {
    if (!walking) return;
    if (i >= todo.size()) {
      startRetry();
      return;
    }
    final Rec r = todo.get(i);
    r.retry = true;
    r.passes++;
    final String name = r == mainRec ? "main match" : shorten(r.rowText);
    matchLabel.setText("Going back  ·  " + name);
    showPage("Opening the page", 0, 1);
    status("Going back to " + name + " (" + (i + 1) + " of " + todo.size() + ", extra pass " + retryPass + ")");
    loadThen(r.url, () -> captureRecord(r, name, () -> {
      finishRecord(r);
      retryRec(todo, i + 1);
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
    jput(mainObj, "played", mainRec.played);
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
    jput(homeObj, "league_code", homeLeague);
    jput(homeObj, "matches", homeArr);
    JSONObject awayObj = new JSONObject();
    jput(awayObj, "name", awayName);
    jput(awayObj, "league_code", awayLeague);
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
    jput(out, "extra_passes", retryPass);
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
    jput(o, "retried", r.retry);
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

  /**
   * Records a tab: captured if it has data, empty if not. A tab that came back empty never
   * replaces data an earlier pass already captured. If the page itself says there is no data,
   * the tab is "nodata": listed as empty, but not a failure.
   */
  private void putLeaf(Rec r, JSONObject parent, String key, String name, String text, boolean empty) {
    if (empty && "captured".equals(r.state.get(name))) return;
    String st = !empty ? "captured" : (hasNoDataLine(text) ? "nodata" : "empty");
    r.state.put(name, st);
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

  /** Records a tab where the page says there is no data. Not a failure. */
  private void putNoData(Rec r, JSONObject parent, String key, String name) {
    if ("captured".equals(r.state.get(name))) return;
    r.state.put(name, "nodata");
    jput(parent, key, leaf("empty", ""));
  }

  /**
   * Records a tab that is not in the page's tab row. This never makes a match incomplete, and
   * it never replaces data an earlier pass captured.
   */
  private void putMissing(Rec r, JSONObject parent, String key, String name) {
    JSONObject cur = parent.optJSONObject(key);
    if (cur != null && !"missing".equals(cur.optString("status"))) return;
    r.state.put(name, "missing");
    jput(parent, key, leaf("missing", ""));
  }

  /** True when a line says there is no data ("No statistics available", and so on). */
  private static boolean hasNoDataLine(String body) {
    if (body == null) return false;
    for (String line : body.split("\n")) {
      if (NO_DATA.matcher(line.trim()).find()) return true;
    }
    return false;
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
// END OF FILE MainActivity.java (v1.2)
