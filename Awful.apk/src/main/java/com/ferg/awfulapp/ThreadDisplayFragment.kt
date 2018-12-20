/********************************************************************************
 * Copyright (c) 2011, Scott Ferguson
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * * Neither the name of the software nor the
 * names of its contributors may be used to endorse or promote products
 * derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY SCOTT FERGUSON ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL SCOTT FERGUSON BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package com.ferg.awfulapp

import android.Manifest
import android.annotation.SuppressLint
import android.app.AlertDialog
import android.app.DownloadManager
import android.app.DownloadManager.Request
import android.content.ContentUris
import android.content.Context
import android.content.Context.DOWNLOAD_SERVICE
import android.content.DialogInterface
import android.content.Intent
import android.content.pm.PackageManager
import android.database.ContentObserver
import android.database.Cursor
import android.graphics.Color
import android.net.Uri
import android.os.AsyncTask
import android.os.Bundle
import android.os.Environment
import android.os.Handler
import android.support.design.widget.FloatingActionButton
import android.support.v4.app.LoaderManager
import android.support.v4.content.ContextCompat
import android.support.v4.content.CursorLoader
import android.support.v4.content.Loader
import android.support.v4.view.MenuItemCompat
import android.support.v7.widget.ShareActionProvider
import android.text.TextUtils
import android.text.format.Formatter
import android.view.InflateException
import android.view.LayoutInflater
import android.view.Menu
import android.view.MenuInflater
import android.view.MenuItem
import android.view.View
import android.view.ViewGroup
import android.webkit.CookieManager
import android.webkit.CookieSyncManager
import android.webkit.JavascriptInterface
import android.webkit.WebView
import android.webkit.WebViewClient
import android.widget.EditText
import android.widget.TextView
import android.widget.Toast

import com.android.volley.VolleyError
import com.crashlytics.android.Crashlytics
import com.ferg.awfulapp.constants.Constants
import com.ferg.awfulapp.network.NetworkUtils
import com.ferg.awfulapp.popupmenu.PostContextMenu
import com.ferg.awfulapp.popupmenu.UrlContextMenu
import com.ferg.awfulapp.preferences.AwfulPreferences
import com.ferg.awfulapp.preferences.Keys
import com.ferg.awfulapp.provider.AwfulProvider
import com.ferg.awfulapp.provider.AwfulTheme
import com.ferg.awfulapp.provider.ColorProvider
import com.ferg.awfulapp.task.AwfulRequest
import com.ferg.awfulapp.task.BookmarkRequest
import com.ferg.awfulapp.task.IgnoreRequest
import com.ferg.awfulapp.task.ImageSizeRequest
import com.ferg.awfulapp.task.MarkLastReadRequest
import com.ferg.awfulapp.task.PostRequest
import com.ferg.awfulapp.task.ProfileRequest
import com.ferg.awfulapp.task.RedirectTask
import com.ferg.awfulapp.task.ReportRequest
import com.ferg.awfulapp.task.SinglePostRequest
import com.ferg.awfulapp.task.ThreadLockUnlockRequest
import com.ferg.awfulapp.task.VoteRequest
import com.ferg.awfulapp.thread.AwfulMessage
import com.ferg.awfulapp.thread.AwfulPagedItem
import com.ferg.awfulapp.thread.AwfulPost
import com.ferg.awfulapp.thread.AwfulThread
import com.ferg.awfulapp.thread.AwfulURL
import com.ferg.awfulapp.thread.AwfulURL.TYPE
import com.ferg.awfulapp.thread.ThreadDisplay
import com.ferg.awfulapp.util.AwfulError
import com.ferg.awfulapp.util.AwfulUtils
import com.ferg.awfulapp.webview.AwfulWebView
import com.ferg.awfulapp.webview.LoggingWebChromeClient
import com.ferg.awfulapp.webview.WebViewJsInterface
import com.ferg.awfulapp.widget.PageBar
import com.ferg.awfulapp.widget.PagePicker
import com.orangegangsters.github.swipyrefreshlayout.library.SwipyRefreshLayout
import com.orangegangsters.github.swipyrefreshlayout.library.SwipyRefreshLayoutDirection

import org.apache.commons.lang3.StringUtils

import java.util.ArrayList
import java.util.HashMap
import java.util.LinkedList

import timber.log.Timber

/**
 * Uses intent extras:
 * TYPE - STRING ID - DESCRIPTION
 * int - Constants.THREAD_ID - id number for that thread
 * int - Constants.THREAD_PAGE - page number to load
 *
 * Can also handle an HTTP intent that refers to an SA showthread.php? url.
 */
class ThreadDisplayFragment : AwfulFragment(), NavigationEventHandler, SwipyRefreshLayout.OnRefreshListener {
    private var mPostLoaderCallback: PostLoaderManager? = null
    private var mThreadLoaderCallback: ThreadDataCallback? = null

    private lateinit var pageBar: PageBar
    private lateinit var userPostNotice: TextView
    private lateinit var FAB: FloatingActionButton
    private lateinit var threadView: AwfulWebView

    /** An optional ID to only display posts by a specific user  */
    private var postFilterUserId: Int? = null
    /** The username to display when filtering by a specific user  */
    private var postFilterUsername: String? = null
    /** Stores the page the user was on before enabling filtering, so they can jump back  */
    private var pageBeforeFiltering = 0


    private var pageNumber = FIRST_PAGE
    var threadId = NULL_THREAD_ID
        private set(aThreadId) {
            field = aThreadId
            (activity as? ForumsIndexActivity)?.onPageContentChanged()
        }

    // TODO: fix this it's all over the place, getting assigned as 1 in loadThread etc - maybe it should default to FIRST_PAGE?
    /** Current thread's last page  */
    private var lastPage = 0
    /**
     * Get the current thread's parent forum's ID.
     *
     * @return the parent forum's ID, or 0 if something went wrong
     */
    var parentForumId = 0
        private set
    private var threadLocked = false
    private var threadBookmarked = false
    private var threadArchived = false
    private var threadLockableUnlockable = false

    private var keepScreenOn = false
    //oh god i'm replicating core android functionality, this is a bad sign.
    private val backStack = LinkedList<AwfulStackEntry>()
    private var bypassBackStack = false

    private var title: String? = null
    // TODO: this strips out any prefix (so it handles prefixed fragments AND bare IDs) and adds the required prefix to all. Might be better to handle this in AwfulURL?
    private var postJump = ""
        set(postJump) {
            field = "post" + postJump.replace("\\D".toRegex(), "")
        }

    private var savedScrollPosition = 0
    private var shareProvider: ShareActionProvider? = null
    private var parentActivity: ForumsIndexActivity? = null
    private var pendingNavigation: NavigationEvent? = null

    private val ignorePostsHtml = HashMap<String, String>()
    private var redirect: AsyncTask<Void, Void, String>? = null
    private var downloadLink: Uri? = null

    private val mThreadObserver = ThreadContentObserver(handler)


    private val threadWebViewClient = object : WebViewClient() {

        override fun shouldOverrideUrlLoading(aView: WebView, aUrl: String): Boolean {
            val aLink = AwfulURL.parse(aUrl)
            when (aLink.type) {
                AwfulURL.TYPE.FORUM -> navigate(NavigationEvent.Forum(aLink.id.toInt(), aLink.page.toInt()))
                AwfulURL.TYPE.THREAD -> if (aLink.isRedirect) {
                    startPostRedirect(aLink.getURL(prefs.postPerPage))
                } else {
                    pushThread(aLink.id.toInt(), aLink.page.toInt(), aLink.fragment.replace("\\D".toRegex(), ""))
                }
                AwfulURL.TYPE.POST -> startPostRedirect(aLink.getURL(prefs.postPerPage))
                AwfulURL.TYPE.EXTERNAL -> if (prefs.alwaysOpenUrls) {
                        startUrlIntent(aUrl)
                    } else {
                        showUrlMenu(aUrl)
                    }
                AwfulURL.TYPE.INDEX -> navigate(NavigationEvent.ForumIndex)
                else -> {}
            }
            return true
        }
    }


    /**
     * General click listener for thread view widgets
     */
    private val clickInterface = ClickInterface()


    /**
     * Get an empty page structure, themed according to the thread's parent forum
     * @return    The basic page HTML, with no post content
     */
    private val blankPage: String
        get() = ThreadDisplay.getContainerHtml(prefs, parentForumId)


    override fun onCreateView(aInflater: LayoutInflater, aContainer: ViewGroup?, aSavedState: Bundle?): View? {
        return try {
            inflateView(R.layout.thread_display, aContainer, aInflater)
        } catch (e: InflateException) {
            if (webViewIsMissing(e)) null
            else throw e
        }
    }


    override fun onViewCreated(view: View, savedInstanceState: Bundle?) {
        super.onViewCreated(view, savedInstanceState)

        pageBar = view.findViewById(R.id.page_bar)
        pageBar.setListener(object : PageBar.PageBarCallbacks {
            override fun onPageNavigation(nextPage: Boolean) {
                turnPage(nextPage)
            }

            override fun onRefreshClicked() {
                refresh()
            }

            override fun onPageNumberClicked() {
                displayPagePicker()
            }
        })
        awfulActivity?.setPreferredFont(pageBar.textView)

        threadView = view.findViewById(R.id.thread)
        initThreadViewProperties()

        userPostNotice = view.findViewById(R.id.thread_userpost_notice)
        refreshProbationBar()

        FAB = view.findViewById(R.id.just_post)
        FAB.setOnClickListener { aView ->
            if(aView.id == R.id.just_post) displayPostReplyDialog()
        }
        FAB.hide()

        allowedSwipeRefreshDirections = SwipyRefreshLayoutDirection.BOTH
        swipyLayout = view.findViewById(R.id.thread_swipe)
        swipyLayout?.setColorSchemeResources(*ColorProvider.getSRLProgressColors(null))
        swipyLayout?.setProgressBackgroundColor(ColorProvider.getSRLBackgroundColor(null))
        swipyLayout?.isEnabled = !prefs.disablePullNext
    }


    override fun onActivityCreated(aSavedState: Bundle?) {
        super.onActivityCreated(aSavedState)

        setHasOptionsMenu(true)
        parentActivity = activity as ForumsIndexActivity?
        mPostLoaderCallback = PostLoaderManager()
        mThreadLoaderCallback = ThreadDataCallback()

        // if a navigation event is pending, we don't care about any saved state - just do the navigation
        if (pendingNavigation != null) {
            Timber.d("Activity attached: found pending navigation event, going there")
            val event = pendingNavigation
            pendingNavigation = null
            navigate(event!!)
            return
        }

        var loadFromCache = false
        if (aSavedState != null) {
            // restoring old state - we have a thread ID and page
            // TODO: 04/05/2017 post filtering state isn't restored properly - need to do filtering AND maintain filtered page/position AND recreate the backstack/'go back' UI
            Timber.i("Restoring fragment - loading cached posts from database")
            threadId = aSavedState.getInt(THREAD_ID_KEY, NULL_THREAD_ID)
            pageNumber = aSavedState.getInt(THREAD_PAGE_KEY, FIRST_PAGE)
            // TODO: 04/05/2017 saved scroll position doesn't seem to actually get used to set the position?
            savedScrollPosition = aSavedState.getInt(SCROLL_POSITION_KEY, 0)
            loadFromCache = true
        }
        // no valid thread ID means do nothing I guess? If the intent that created the activity+fragments didn't request a thread
        if (threadId <= 0) {
            return
        }
        // if we recreated the fragment (and had a valid thread ID) we just want to load the cached page data,
        // so we get the same state as before (we don't want to reload the page and e.g. have all the posts marked as seen)
        if (loadFromCache) {
            refreshPosts()
            refreshInfo()
        } else {
            syncThread()
        }
        updateUiElements()
    }


    /**
     * Check if an InflateException is caused by a missing WebView.
     *
     *
     * Also displays a message for the user.
     *
     * @param e the exception thrown when inflating the layout
     * @return true if the WebView is missing
     */
    private fun webViewIsMissing(e: InflateException): Boolean {
        val message = e.message

        if (message == null || !message.toLowerCase().contains("webview")) {
            return false
        }
        Timber.w("Can't inflate thread view, WebView package is updating?:\n")
        e.printStackTrace()
        alertView
                .setIcon(R.drawable.ic_error)
                .setTitle(R.string.web_view_missing_alert_title)
                .setSubtitle(R.string.web_view_missing_alert_message)
                .show()
        return true
    }


    private fun initThreadViewProperties() {
        threadView.webViewClient = threadWebViewClient
        threadView.webChromeClient = object : LoggingWebChromeClient(threadView) {
            override fun onProgressChanged(view: WebView, newProgress: Int) {
                super.onProgressChanged(view, newProgress)
                setProgress(newProgress / 2 + 50)//second half of progress bar
            }
        }
        threadView.setJavascriptHandler(clickInterface)

        refreshSessionCookie()
        Timber.d("Setting up WebView container HTML")
        threadView.setContent(blankPage)
        threadView.setDownloadListener { url, _, _, _, _ -> enqueueDownload(Uri.parse(url)) }

    }

    private fun updatePageBar() {
        pageBar.updatePagePosition(pageNumber, lastPage)
        invalidateOptionsMenu()
        swipyLayout?.setOnRefreshListener(if (prefs.disablePullNext) null else this)
    }


    override fun onResume() {
        super.onResume()
        threadView.onResume()
        activity?.contentResolver?.registerContentObserver(AwfulThread.CONTENT_URI, true, mThreadObserver)
        refreshInfo()
    }


    override fun setAsFocusedPage() {
        threadView.onResume()
        threadView.keepScreenOn = keepScreenOn
    }

    override fun setAsBackgroundPage() {
        threadView.keepScreenOn = false
        threadView.onPause()
    }

    override fun onPause() {
        super.onPause()
        activity?.contentResolver?.unregisterContentObserver(mThreadObserver)
        loaderManager.destroyLoader(Constants.THREAD_INFO_LOADER_ID)
        threadView.onPause()
    }

    override fun cancelNetworkRequests() {
        super.cancelNetworkRequests()
        NetworkUtils.cancelRequests(PostRequest.REQUEST_TAG)
    }


    override fun onDestroy() {
        super.onDestroy()
        loaderManager.destroyLoader(Constants.POST_LOADER_ID)
    }

    // TODO: fix deprecated warnings
    @Synchronized
    private fun refreshSessionCookie() {
        Timber.e("refreshing cookies")
        val cookieMonster = CookieManager.getInstance()
        cookieMonster.removeAllCookies(null)
        cookieMonster.setCookie(Constants.COOKIE_DOMAIN, NetworkUtils.getCookieString(Constants.COOKIE_NAME_SESSIONID))
        cookieMonster.setCookie(Constants.COOKIE_DOMAIN, NetworkUtils.getCookieString(Constants.COOKIE_NAME_SESSIONHASH))
        cookieMonster.setCookie(Constants.COOKIE_DOMAIN, NetworkUtils.getCookieString(Constants.COOKIE_NAME_USERID))
        cookieMonster.setCookie(Constants.COOKIE_DOMAIN, NetworkUtils.getCookieString(Constants.COOKIE_NAME_PASSWORD))
        cookieMonster.setAcceptThirdPartyCookies(threadView, true)
        CookieManager.getInstance().flush()
    }


    override fun onCreateOptionsMenu(menu: Menu?, inflater: MenuInflater?) {
        menu?.clear()
        if (menu?.size() == 0) {
            inflater?.inflate(R.menu.post_menu, menu)
            val share = menu.findItem(R.id.share_thread)
            if (share != null && MenuItemCompat.getActionProvider(share) is ShareActionProvider) {
                shareProvider = MenuItemCompat.getActionProvider(share) as ShareActionProvider
                shareProvider?.setShareIntent(createShareIntent(null))
            }
        }
    }

    override fun onPrepareOptionsMenu(menu: Menu?) {
        if (menu == null || activity == null) {
            return
        }
        val lockUnlock = menu.findItem(R.id.lock_unlock)
        lockUnlock?.isVisible = threadLockableUnlockable
        lockUnlock?.title = if (threadLocked) getString(R.string.thread_unlock) else getString(R.string.thread_lock)

        val find = menu.findItem(R.id.find)
        find?.isVisible = true

        val reply = menu.findItem(R.id.reply)
        reply?.isVisible = prefs.noFAB

        val bk = menu.findItem(R.id.bookmark)
        if (threadArchived) {
            bk?.title = getString(R.string.bookmarkarchived)
        } else {
            bk?.title = if (threadBookmarked) getString(R.string.unbookmark) else getString(R.string.bookmark)
        }
        bk?.isEnabled = !threadArchived

        val screen = menu.findItem(R.id.keep_screen_on)
        screen?.isChecked = keepScreenOn

        val yospos = menu.findItem(R.id.yospos)
        yospos?.isVisible = parentForumId == Constants.FORUM_ID_YOSPOS
    }

    override fun onOptionsItemSelected(item: MenuItem?): Boolean {
        when (item?.itemId) {
            R.id.lock_unlock -> showThreadLockUnlockDialog()
            R.id.reply -> displayPostReplyDialog()
            R.id.next_page -> turnPage(true)
            R.id.rate_thread -> rateThread()
            R.id.copy_url -> copyThreadURL(null)
            R.id.find -> this.threadView.showFindDialog(null, true)
            R.id.keep_screen_on -> {
                this.toggleScreenOn()
                item.isChecked = !item.isChecked
            }
            R.id.bookmark -> toggleThreadBookmark()
            R.id.yospos -> toggleYospos()
            else -> return super.onOptionsItemSelected(item)
        }

        return true
    }


    /**
     * Get a URL that links to a particular thread.
     *
     * @param postId An optional post ID, appended as the URL's fragment
     * @return the full URL
     */
    private fun generateThreadUrl(postId: Int?): String {
        val builder = Uri.parse(Constants.FUNCTION_THREAD).buildUpon()
                .appendQueryParameter(Constants.PARAM_THREAD_ID, threadId.toString())
                .appendQueryParameter(Constants.PARAM_PAGE, pageNumber.toString())
                .appendQueryParameter(Constants.PARAM_PER_PAGE, prefs.postPerPage.toString())
        if (postId != null) {
            builder.fragment("post$postId")
        }
        return builder.toString()
    }


    /**
     * Get a URL that links to a particular post.
     *
     * @param postId The ID of the post to link to
     * @return the full URL
     */
    private fun generatePostUrl(postId: Int): String {
        return Uri.parse(Constants.FUNCTION_THREAD).buildUpon()
                .appendQueryParameter(Constants.PARAM_GOTO, Constants.VALUE_POST)
                .appendQueryParameter(Constants.PARAM_POST_ID, Integer.toString(postId))
                .toString()
    }


    /**
     * Get a share intent for a url.
     *
     *
     * If url is null, a link to the current thread will be generated.
     *
     * @param url The url to share
     */
    fun createShareIntent(url: String?): Intent {
        var url = url
        val intent = Intent(Intent.ACTION_SEND).setType("text/plain")
        if (url == null) {
            // we're sharing the current thread - we can add the title in here
            intent.putExtra(Intent.EXTRA_SUBJECT, title)
            url = generateThreadUrl(null)
        }
        return intent.putExtra(Intent.EXTRA_TEXT, url)
    }


    /**
     * Copy a thread's URL to the clipboard
     * @param postId    An optional post ID, used as the url's fragment
     */
    fun copyThreadURL(postId: Int?) {
        val clipLabel = getString(R.string.copy_url) + pageNumber
        val clipText = generateThreadUrl(postId)
        safeCopyToClipboard(clipLabel, clipText, R.string.copy_url_success)
    }


    /**
     * Display a thread-rating dialog.
     *
     * This handles the network request to submit the vote, and user feedback.
     */
    private fun rateThread() {
        val items = arrayOf<CharSequence>("1", "2", "3", "4", "5")
        val activity = this.activity

        AlertDialog.Builder(activity)
                .setTitle("Rate this thread")
                .setItems(items) { dialog, item ->
                    queueRequest(VoteRequest(activity, threadId, item)
                            .build(this@ThreadDisplayFragment, object : AwfulRequest.AwfulResultCallback<Void> {
                                override fun success(result: Void) {
                                    alertView.setTitle(R.string.vote_succeeded)
                                            .setSubtitle(R.string.vote_succeeded_sub)
                                            .setIcon(R.drawable.ic_mood)
                                            .show()
                                }


                                override fun failure(error: VolleyError) {}
                            }))
                }.show()
    }


    /**
     * Add a user to the ignore list.
     *
     * @param userId The awful ID of the user
     */
    fun ignoreUser(userId: Int) {
        val activity = activity
        if (prefs.ignoreFormkey == null) {
            queueRequest(ProfileRequest(activity, null).build())
        }
        if (prefs.showIgnoreWarning) {

            val onClickListener = { dialog: DialogInterface, which: Int ->
                if (which == AlertDialog.BUTTON_NEUTRAL) {
                    // cancel future alerts if the user clicks the "don't warn" option
                    prefs.setPreference(Keys.SHOW_IGNORE_WARNING, false)
                }
                doIgnoreUser(activity!!, userId)
            }

            AlertDialog.Builder(activity)
                    .setPositiveButton(R.string.confirm, onClickListener)
                    .setNeutralButton(R.string.dont_show_again, onClickListener)
                    .setNegativeButton(R.string.cancel, null)
                    .setTitle(R.string.ignore_title)
                    .setMessage(R.string.ignore_message)
                    .show()
        } else {
            doIgnoreUser(activity!!, userId)
        }
    }


    /**
     * Carry out the ignore user request
     */
    private fun doIgnoreUser(context: Context, userId: Int) {
        //we don't care about status callbacks for this, so we use the build() that doesn't do callbacks
        queueRequest(IgnoreRequest(context, userId).build())
    }


    /**
     * Toggle a user as marked or unmarked.
     */
    fun toggleMarkUser(username: String) {
        if (prefs.markedUsers.contains(username)) {
            prefs.unmarkUser(username)
        } else {
            prefs.markUser(username)
        }
    }


    /**
     * Toggle between displaying a single user's posts, or all posts
     * @param aPostId    The ID of the post to display, if toggling filtering off
     * @param aUserId    The ID of the user whose posts we're showing, if toggling on
     * @param aUsername    The username of the user, if toggling on
     */
    // TODO: refactor this and the methods it calls - it's so weird
    fun toggleUserPosts(aPostId: Int, aUserId: Int, aUsername: String) {
        if (postFilterUserId != null) {
            showAllPosts(aPostId)
        } else {
            showUsersPosts(aUserId, aUsername)
        }
    }


    /**
     * Display a dialog to report a post
     *
     * @param postId    The ID of the bad post
     */
    fun reportUser(postId: Int) {
        val reportReason = EditText(this.activity)

        AlertDialog.Builder(this.activity)
                .setTitle("Report inappropriate post")
                .setMessage("Did this post break the forum rules? If so, please report it by clicking below. If you would like to add any comments explaining why you submitted this post, please do so here:")
                .setView(reportReason)
                .setPositiveButton("Report") { dialog, whichButton ->
                    val reason = reportReason.text.toString()
                    queueRequest(ReportRequest(activity, postId, reason).build(this@ThreadDisplayFragment, object : AwfulRequest.AwfulResultCallback<String> {
                        override fun success(result: String) {
                            alertView.setTitle(result).setIcon(R.drawable.ic_mood).show()
                        }

                        override fun failure(error: VolleyError) {
                            alertView.setTitle(error.message).setIcon(R.drawable.ic_mood).show()

                        }
                    }))
                }
                .setNegativeButton(R.string.cancel, null)
                .show()
    }

    override fun onSaveInstanceState(outState: Bundle) {
        super.onSaveInstanceState(outState)
        Timber.d("onSaveInstanceState - storing thread ID, page number and scroll position")
        outState.putInt(THREAD_ID_KEY, threadId)
        outState.putInt(THREAD_PAGE_KEY, pageNumber)
        outState.putInt(SCROLL_POSITION_KEY, threadView.scrollY)
    }


    /**
     * Reload the current thread page
     */
    private fun syncThread() {
        val activity = activity
        if (activity != null) {
            Timber.i("Syncing - reloading from site (thread %d, page %d) to update DB", threadId, pageNumber)
            // cancel pending post loading requests
            NetworkUtils.cancelRequests(PostRequest.REQUEST_TAG)
            // call this with cancelOnDestroy=false to retain the request's specific type tag
            val pageNumber = pageNumber
            val userId = postFilterUserId ?: BLANK_USER_ID
            queueRequest(PostRequest(activity, threadId, pageNumber, userId)
                    .build(this, object : AwfulRequest.AwfulResultCallback<Int> {
                        override fun success(result: Int?) {
                            refreshInfo()
                            setProgress(75)
                            refreshPosts()
                        }

                        override fun failure(error: VolleyError) {
                            Timber.w("Failed to sync thread! Error: %s", error.message)
                            refreshInfo()
                            refreshPosts()
                        }
                    }), false)
        }
    }


    /**
     * Mark a post as the last read in this thread.
     *
     *
     * This takes an attribute in the HTML called `data-idx`, which is basically
     * an enumeration of the posts in the thread.
     *
     * @param index The `data-idx` value of the post.
     */
    @SuppressLint("BinaryOperationInTimber")
    fun markLastRead(index: Int) {
        alertView.setTitle(R.string.mark_last_read_progress)
                .setSubtitle(R.string.please_wait_subtext)
                .setIcon(R.drawable.ic_visibility)
                .show()

        queueRequest(MarkLastReadRequest(activity, threadId, index)
                .build(null, object : AwfulRequest.AwfulResultCallback<Void?> {
                    override fun success(result: Void?) {
                        if (activity != null) {
                            alertView.setTitle(R.string.mark_last_read_success)
                                    .setIcon(R.drawable.ic_visibility)
                                    .show()
                            refreshInfo()
                            refreshPosts()
                        }
                    }


                    override fun failure(error: VolleyError) {
                    }
                }))
    }


    /**
     * Toggle this thread's bookmarked status.
     */
    private fun toggleThreadBookmark() {
        val activity = activity
        if (activity != null) {
            queueRequest(BookmarkRequest(activity, threadId, !threadBookmarked)
                    .build(this, object : AwfulRequest.AwfulResultCallback<Void> {
                        override fun success(result: Void) {
                            refreshInfo()
                        }

                        override fun failure(error: VolleyError) {
                            refreshInfo()
                        }
                    }))
        }
    }


    /**
     * Toggle between amberPOS and greenPOS, refreshing the display.
     */
    private fun toggleYospos() {
        prefs.amberDefaultPos = !prefs.amberDefaultPos
        prefs.setPreference(Keys.AMBER_DEFAULT_POS, prefs.amberDefaultPos)
        threadView.runJavascript(String.format("changeCSS('%s')", AwfulTheme.forForum(parentForumId).cssPath))
    }


    /**
     * Reload with a new URL
     * @param postUrl    The URL of the post we should land on
     */
    private fun startPostRedirect(postUrl: String) {
        val activity = awfulActivity ?: return
        redirect?.cancel(false)

        setProgress(50)
        redirect = object : RedirectTask(postUrl) {
            override fun onPostExecute(url: String?) {
                if (isCancelled) {
                    return
                } else if (url == null) {
                    alertView.show(AwfulError())
                    return
                }

                val result = AwfulURL.parse(url)
                if (postUrl.contains(Constants.VALUE_LASTPOST)) {
                    //This is a workaround for how the forums handle the perPage value with goto=lastpost.
                    //The redirected url is lacking the perpage=XX value.
                    //We just override the assumed (40) with the number we requested when starting the redirect.
                    //I gotta ask chooch to fix this at some point.
                    result.setPerPage(prefs.postPerPage)
                }
                if (result.type == TYPE.THREAD) {
                    val threadId = result.id.toInt()
                    val threadPage = result.getPage(prefs.postPerPage).toInt()
                    val postJump = result.fragment
                    if (bypassBackStack) {
                        openThread(threadId, threadPage, postJump)
                    } else {
                        pushThread(threadId, threadPage, postJump)
                    }
                } else if (result.type == TYPE.INDEX) {
                    activity.navigate(NavigationEvent.ForumIndex)
                }
                redirect = null
                bypassBackStack = false
                setProgress(100)
            }
        }.execute()
    }


    /**
     * Show the page picker dialog, and handle user input and navigation.
     */
    private fun displayPagePicker() {
        val activity = activity ?: return

        PagePicker(activity, lastPage, pageNumber) { button, resultValue ->
            if (button == DialogInterface.BUTTON_POSITIVE) {
                goToPage(resultValue)
            }
        }.show()
    }


    override fun onActivityResult(aRequestCode: Int, aResultCode: Int, aData: Intent?) {
        Timber.d("onActivityResult - request code: %d, result: %d", aRequestCode, aResultCode)
        // If we're here because of a post result, refresh the thread
        when (aRequestCode) {
            PostReplyFragment.REQUEST_POST -> {
                bypassBackStack = true
                if (aResultCode == PostReplyFragment.RESULT_POSTED) {
                    startPostRedirect(AwfulURL.threadLastPage(threadId.toLong(), prefs.postPerPage).getURL(prefs.postPerPage))
                } else if (aResultCode > 100) {//any result >100 it is a post id we edited
                    // TODO: >100 is a bit too magical
                    startPostRedirect(AwfulURL.post(aResultCode.toLong(), prefs.postPerPage).getURL(prefs.postPerPage))
                }
            }
        }
    }


    /**
     * Refresh the page
     */
    private fun refresh() {
        showBlankPage()
        syncThread()
    }


    /**
     * Load the next or previous page.
     *
     * The current page will reload if there is no next/previous page to move to.
     */
    private fun turnPage(forwards: Boolean) {
        val currentPage = pageNumber
        val limit = if (forwards) lastPage else FIRST_PAGE
        if (currentPage == limit) {
            refresh()
        } else {
            goToPage(currentPage + if (forwards) 1 else -1)
        }
    }

    private fun displayPostReplyDialog() {
        displayPostReplyDialog(threadId, -1, AwfulMessage.TYPE_NEW_REPLY)
    }


    /**
     * Show a dialog that allows the user to lock or unlock the current thread, as appropriate.
     */
    private fun showThreadLockUnlockDialog() {
        AlertDialog.Builder(activity)
                .setTitle(getString(if (threadLocked) R.string.thread_unlock else R.string.thread_lock) + "?")
                .setPositiveButton(R.string.alert_ok) { dialogInterface, i -> toggleThreadLock() }
                .setNegativeButton(R.string.cancel, null)
                .show()
    }


    /**
     * Trigger a request to toggle the current thread's locked/unlocked state.
     */
    private fun toggleThreadLock() {
        queueRequest(ThreadLockUnlockRequest(activity, threadId).build(this, object : AwfulRequest.AwfulResultCallback<Void> {
            override fun success(result: Void) {
                // TODO: maybe this should trigger a thread data refresh instead, update everything from the source
                threadLocked = !threadLocked
            }

            override fun failure(error: VolleyError) {
                Timber.e(String.format("Couldn\'t %s this thread", if (threadLocked) "unlock" else "lock"))
            }
        }))
    }

    private fun populateThreadView(aPosts: ArrayList<AwfulPost>) {
        updateUiElements()

        try {
            Timber.d("populateThreadView: displaying %d posts", aPosts.size)
            val html = ThreadDisplay.getHtml(aPosts, AwfulPreferences.getInstance(activity), pageNumber, lastPage)
            refreshSessionCookie()
            threadView.setBodyHtml(html)
            setProgress(100)
        } catch (e: Exception) {
            // If we've already left the activity the webview may still be working to populate,
            // just log it
            Timber.e(e, "populateThreadView: display failed")
        }

    }

    override fun onRefresh(swipyRefreshLayoutDirection: SwipyRefreshLayoutDirection) {
        if (swipyRefreshLayoutDirection == SwipyRefreshLayoutDirection.TOP) {
            refresh()
        } else {
            turnPage(true)
        }
    }

    private inner class ClickInterface : WebViewJsInterface() {

        val css: String
            @JavascriptInterface
            get() = AwfulTheme.forForum(parentForumId).cssPath

        @JavascriptInterface
        fun onMoreClick(aPostId: String, aUsername: String, aUserId: String, lastReadUrl: String, editable: Boolean, isAdminOrMod: Boolean, isPlat: Boolean) {
            val postActions = PostContextMenu.newInstance(threadId, Integer.parseInt(aPostId),
                    Integer.parseInt(lastReadUrl), editable, aUsername, Integer.parseInt(aUserId), isPlat, isAdminOrMod)
            postActions.setTargetFragment(this@ThreadDisplayFragment, -1)
            postActions.show(fragmentManager!!, "Post Actions")
        }


        override fun setCustomPreferences(preferences: MutableMap<String, String>) {
            // TODO: 23/01/2017 add methods so you can't mess with the map directly
            preferences["postjumpid"] = postJump
            preferences["scrollPosition"] = Integer.toString(savedScrollPosition)
        }

        @JavascriptInterface
        fun getIgnorePostHtml(id: String): String {
            return ignorePostsHtml[id]!!
        }


        @JavascriptInterface
        fun loadIgnoredPost(ignorePost: String) {
            if (activity != null) {
                queueRequest(SinglePostRequest(activity, ignorePost).build(this@ThreadDisplayFragment, object : AwfulRequest.AwfulResultCallback<String> {
                    override fun success(result: String) {
                        ignorePostsHtml[ignorePost] = result
                        threadView.runJavascript(String.format("insertIgnoredPost('%s')", ignorePost))
                    }

                    override fun failure(error: VolleyError) {
                        Timber.w("Failed to load ignored post #$ignorePost")
                    }
                }))
            }
        }

        @JavascriptInterface
        fun haltSwipe() {
            (this@ThreadDisplayFragment.awfulActivity as ForumsIndexActivity).preventSwipe()
        }

        @JavascriptInterface
        fun resumeSwipe() {
            (this@ThreadDisplayFragment.awfulActivity as ForumsIndexActivity).allowSwipe()
        }

        @JavascriptInterface
        fun popupText(text: String) {
            Toast.makeText(activity, text, Toast.LENGTH_SHORT).show()
        }

        @JavascriptInterface
        fun openUrlMenu(url: String) {
            showUrlMenu(url)
        }
    }


    private fun showUrlMenu(url: String?) {
        if (url == null) {
            Timber.w("Passed null URL to #showUrlMenu!")
            return
        }
        val fragmentManager = fragmentManager
        if (fragmentManager == null) {
            Timber.w("showUrlMenu called but can't get FragmentManager!")
            return
        }

        var isImage = false
        var isGif = false
        // TODO: parsing fails on magic webdev urls like http://tpm2016.zoffix.com/#/40
        // it thinks the # is the start of the ref section of the url, so the Path for that url is '/'
        val path = Uri.parse(url)
        var lastSegment = path.lastPathSegment
        // null-safe path checking (there may be no path segments, e.g. a link to a domain name)
        if (lastSegment != null) {
            lastSegment = lastSegment.toLowerCase()
            // using 'contains' instead of 'ends with' in case of any url suffix shenanigans, like twitter's ".jpg:large"
            isImage = StringUtils.indexOfAny(lastSegment, ".jpg", ".jpeg", ".png", ".gif") != -1 && !StringUtils.contains(lastSegment, ".gifv") || lastSegment == "attachment.php" && path.host == "forums.somethingawful.com"
            isGif = StringUtils.contains(lastSegment, ".gif") && !StringUtils.contains(lastSegment, ".gifv")
        }

        ////////////////////////////////////////////////////////////////////////
        // TODO: 28/04/2017 remove all this when Crashlytics #717 is fixed
        if (AwfulApplication.crashlyticsEnabled()) {
            Crashlytics.setString("Menu for URL:", url)
            Crashlytics.setInt("Thread ID", threadId)
            Crashlytics.setInt("Page", pageNumber)

            val activity = activity
            Crashlytics.setBool("Activity exists", activity != null)
            if (activity != null) {
                var state = "Activity:"
                state += if (activity.isDestroyed) "IS_DESTROYED " else ""
                state += if (activity.isFinishing) "IS_FINISHING" else ""
                state += if (activity.isChangingConfigurations) "IS_CHANGING_CONFIGURATIONS" else ""
                Crashlytics.setString("Activity state:", state)
            }
            Crashlytics.setBool("Thread display fragment resumed", isResumed)
            Crashlytics.setBool("Thread display fragment attached", isAdded)
            Crashlytics.setBool("Thread display fragment removing", isRemoving)
        }
        ////////////////////////////////////////////////////////////////////////

        val linkActions = UrlContextMenu.newInstance(url, isImage, isGif, if (isGif) "Getting file size" else null)

        if (isGif || !AwfulPreferences.getInstance().canLoadImages()) {
            queueRequest(ImageSizeRequest(url)  { result ->
                if (linkActions == null) {
                    return@ImageSizeRequest
                }
                val size = if (result == null) "unknown" else Formatter.formatShortFileSize(context, result.toLong())
                linkActions.setSubheading(String.format("Size: %s", size))
            })
        }
        linkActions.setTargetFragment(this@ThreadDisplayFragment, -1)
        linkActions.show(fragmentManager, "Link Actions")
    }

    fun showImageInline(url: String) {
        threadView.runJavascript(String.format("showInlineImage('%s')", url))
    }

    fun enqueueDownload(link: Uri) {
        if (AwfulUtils.isMarshmallow()) {
            val permissionCheck = ContextCompat.checkSelfPermission(this.context!!, Manifest.permission.WRITE_EXTERNAL_STORAGE)
            if (permissionCheck != PackageManager.PERMISSION_GRANTED) {
                downloadLink = link
                requestPermissions(arrayOf(Manifest.permission.WRITE_EXTERNAL_STORAGE), Constants.AWFUL_PERMISSION_WRITE_EXTERNAL_STORAGE)
                return
            }
        }
        val request = Request(link)
        request.setNotificationVisibility(Request.VISIBILITY_VISIBLE_NOTIFY_COMPLETED)
        if (link.lastPathSegment == "attachment.php" && link.host == "forums.somethingawful.com") {
            request.setDestinationInExternalPublicDir(Environment.DIRECTORY_DOWNLOADS, "attachment.png")
            request.addRequestHeader("Cookie", CookieManager.getInstance().getCookie(Constants.COOKIE_DOMAIN))
        } else {
            request.setDestinationInExternalPublicDir(Environment.DIRECTORY_DOWNLOADS, link.lastPathSegment)
        }
        request.allowScanningByMediaScanner()
        val dlManager = awfulActivity?.getSystemService(DOWNLOAD_SERVICE) as DownloadManager?
        dlManager?.enqueue(request)
    }

    fun copyToClipboard(text: String) {
        safeCopyToClipboard("Copied URL", text, null)
        alertView
                .setTitle(R.string.copy_url_success)
                .setIcon(R.drawable.ic_insert_link)
                .show()
    }

    fun startUrlIntent(url: String) {
        val browserIntent = Intent(Intent.ACTION_VIEW, Uri.parse(url))
        val pacMan = activity!!.packageManager
        val res = pacMan.queryIntentActivities(browserIntent,
                PackageManager.MATCH_DEFAULT_ONLY)
        if (res.size > 0) {
            browserIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
            activity!!.startActivity(browserIntent)
        } else {
            val split = url.split(":".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
            alertView.setTitle("Cannot open link:")
                    .setSubtitle("No application found for protocol" + if (split.size > 0) ": " + split[0] else ".")
                    .show()
        }
    }

    fun displayImage(url: String) {
        val intent = BasicActivity.intentFor(ImageViewFragment::class.java, activity!!, "")
        intent.putExtra(ImageViewFragment.EXTRA_IMAGE_URL, url)
        startActivity(intent)
    }

    override fun onPreferenceChange(prefs: AwfulPreferences, key: String?) {
        super.onPreferenceChange(prefs, key)
        Timber.i("onPreferenceChange" + if (key != null) ":$key" else "")
        awfulActivity?.setPreferredFont(pageBar.textView)
        pageBar.setTextColour(ColorProvider.ACTION_BAR_TEXT.color)

        threadView.setBackgroundColor(Color.TRANSPARENT)
        threadView.runJavascript(String.format("changeFontFace('%s')", prefs.preferredFont))
        threadView.settings?.defaultFontSize = prefs.postFontSizeSp
        threadView.settings?.defaultFixedFontSize = prefs.postFixedFontSizeSp

        if ("marked_users" == key) {
            threadView.runJavascript(String.format("updateMarkedUsers('%s')", TextUtils.join(",", prefs.markedUsers)))
        }

        clickInterface.updatePreferences()
        if (prefs.noFAB) {
            FAB.hide()
        } else {
            FAB.show()
        }
    }


    /**
     * Update any UI elements that need to be refreshed.
     */
    private fun updateUiElements() {
        // TODO: probably more things can be put in here, there's a lot to unravel
        updatePageBar()
        refreshProbationBar()
    }


    /**
     * Load a specific page in the current thread.
     *
     * This method does nothing if the page number is not valid (i.e. between [.FIRST_PAGE] and the last page).
     * @param aPage    a page number for this thread
     */
    private fun goToPage(aPage: Int) {
        if (aPage <= 0 || aPage > lastPage) {
            return
        }
        pageNumber = aPage
        updateUiElements()
        postJump = ""
        showBlankPage()
        syncThread()
    }


    /**
     * Show posts filtered to a specific user
     * @param id    the user's ID
     * @param name    the user's username
     */
    private fun showUsersPosts(id: Int, name: String) {
        // TODO: legend has it this doesn't work and shows other people's posts if the page isn't full
        pageBeforeFiltering = pageNumber
        setPostFiltering(id, name)
        pageNumber = FIRST_PAGE
        lastPage = FIRST_PAGE
        postJump = ""
        refresh()
    }


    /**
     * Clear filtering added by [.showUsersPosts] and return to a specific post
     * @param postId    The ID of the post to navigate to
     */
    private fun showAllPosts(postId: Int?) {
        if (postId != null) {
            showBlankPage()
            openThread(AwfulURL.parse(generatePostUrl(postId)))
        } else {
            setPostFiltering(null, null)
            pageNumber = pageBeforeFiltering
            lastPage = 0
            postJump = ""
            refresh()
        }
    }


    /**
     * Set or unset the "show user's posts" filtering state.
     * @param userId    The ID of the user to filter to, or null for no filtering
     * @param username    The username of the user. If ID is null, this is ignored
     */
    private fun setPostFiltering(userId: Int?, username: String?) {
        postFilterUserId = userId
        postFilterUsername = if (userId == null) null else username
    }


    /**
     * Clear the thread display, e.g. to show a blank page before loading new content
     */
    private fun showBlankPage() {
        threadView.setBodyHtml(null)
    }


    private inner class PostLoaderManager : LoaderManager.LoaderCallbacks<Cursor> {
        override fun onCreateLoader(aId: Int, aArgs: Bundle?): Loader<Cursor> {
            val index = AwfulPagedItem.pageToIndex(pageNumber, prefs.postPerPage, 0)
            Timber.i("Loading page %d of thread %d from database\nStart index is %d with %d posts per page",
                    pageNumber, threadId, index, prefs.postPerPage)
            return CursorLoader(activity!!,
                    AwfulPost.CONTENT_URI,
                    AwfulProvider.PostProjection,
                    selection,
                    AwfulProvider.int2StrArray(threadId, index, index + prefs.postPerPage),
                    sortOrder)
        }

        override fun onLoadFinished(aLoader: Loader<Cursor>, aData: Cursor) {
            setProgress(90)
            if (aData.isClosed) {
                return
            }

            populateThreadView(AwfulPost.fromCursor(activity, aData))

            // TODO: 04/05/2017 sometimes you don't want this resetting, e.g. restoring fragment state
            savedScrollPosition = 0
        }

        override fun onLoaderReset(aLoader: Loader<Cursor>) {}
    }


    private inner class ThreadDataCallback : LoaderManager.LoaderCallbacks<Cursor> {

        override fun onCreateLoader(aId: Int, aArgs: Bundle?): Loader<Cursor> {
            return CursorLoader(activity!!, ContentUris.withAppendedId(AwfulThread.CONTENT_URI, threadId.toLong()),
                    AwfulProvider.ThreadProjection, null, null, null)
        }

        override fun onLoadFinished(aLoader: Loader<Cursor>, aData: Cursor) {
            Timber.i("Loaded thread metadata, updating fragment state and UI")
            if (aData.count > 0 && aData.moveToFirst()) {
                lastPage = AwfulPagedItem.indexToPage(aData.getInt(aData.getColumnIndex(AwfulThread.POSTCOUNT)), prefs.postPerPage)
                threadLocked = aData.getInt(aData.getColumnIndex(AwfulThread.LOCKED)) > 0
                threadLockableUnlockable = aData.getInt(aData.getColumnIndex(AwfulThread.CAN_OPEN_CLOSE)) > 0
                threadBookmarked = aData.getInt(aData.getColumnIndex(AwfulThread.BOOKMARKED)) > 0
                threadArchived = aData.getInt(aData.getColumnIndex(AwfulThread.ARCHIVED)) > 0
                title = aData.getString(aData.getColumnIndex(AwfulThread.TITLE))
                parentForumId = aData.getInt(aData.getColumnIndex(AwfulThread.FORUM_ID))
                if (parentForumId != 0) {
                    threadView.runJavascript(String.format("changeCSS('%s')", AwfulTheme.forForum(parentForumId).cssPath))
                }

                parentActivity?.onPageContentChanged()

                updateUiElements()

                userPostNotice.apply {
                    if (postFilterUserId != null) {
                        visibility = View.VISIBLE
                        text = String.format("Viewing posts by %s in this thread,\nPress the back button to return.", postFilterUsername)
                        setTextColor(ColorProvider.PRIMARY_TEXT.color)
                        setBackgroundColor(ColorProvider.BACKGROUND.color)
                    } else {
                        visibility = View.GONE
                    }
                }

                shareProvider?.setShareIntent(createShareIntent(null))

                invalidateOptionsMenu()
                if (prefs.noFAB || threadLocked || threadArchived) {
                    FAB.hide()
                } else {
                    FAB.show()
                }
            }
        }

        override fun onLoaderReset(aLoader: Loader<Cursor>) {}
    }

    private inner class ThreadContentObserver(aHandler: Handler) : ContentObserver(aHandler) {
        override fun onChange(selfChange: Boolean) {
            Timber.i("Thread metadata has been updated - forcing refresh")
            refreshInfo()
        }
    }

    /**
     * Refresh the displayed thread's data (bookmarked, locked etc.)
     *
     * This loads from the database, and reflects the last cached status of the thread.
     * To actually download current data from the site call [.syncThread] instead.
     * @see ThreadDataCallback
     */
    private fun refreshInfo() {
        restartLoader(Constants.THREAD_INFO_LOADER_ID, null, mThreadLoaderCallback!!)
    }


    /**
     * Refresh the posts displayed, according to current setting (thread ID, page etc.)
     *
     * This loads from the database, and reflects the last cached view of the thread.
     * To actually download updated data (including changes in posts' viewed status) call
     * [.syncThread] instead.
     * @see PostLoaderManager
     */
    private fun refreshPosts() {
        restartLoader(Constants.POST_LOADER_ID, null, mPostLoaderCallback!!)
    }


    fun setTitle(title: String) {
        this.title = title
        parentActivity?.onPageContentChanged()
    }


    override fun getTitle() = title


    override fun handleNavigation(event: NavigationEvent): Boolean {
        // need to check if the fragment is attached to the activity - if not, defer any handled events until it is attached
        if (event is NavigationEvent.Thread) {
            if (!isAdded) {
                deferNavigation(event)
            } else {
                val (id, page, postJump1) = event
                openThread(id, page, postJump1)
            }
            return true
        } else if (event is NavigationEvent.Url) {
            if (!isAdded) {
                deferNavigation(event)
            } else {
                openThread(event.url)
            }
            return true
        }
        return false
    }

    /**
     * Store a navigation event for handling when this fragment is attached to the activity
     */
    private fun deferNavigation(event: NavigationEvent) {
        Timber.d("Deferring navigation event(%s) - isAdded = %b", event, isAdded)
        pendingNavigation = event
    }


    /**
     * Open a thread, jumping to a specific page and post if required.
     * @param id        The thread's ID
     * @param page        An optional page to display, otherwise it defaults to the first page
     * @param postJump    An optional URL fragment representing the post ID to jump to
     */
    private fun openThread(id: Int, page: Int?, postJump: String?) {
        Timber.i("Opening thread (old/new) ID:%d/%d, PAGE:%s/%s, JUMP:%s/%s",
                threadId, id, pageNumber, page, postJump, postJump)
        // removed because it included (if !forceReload) and that param was always set to true
        //		if (id == currentThreadId && (page == null || page == currentPage)) {
        //			// do nothing if there's no change
        //			// TODO: 15/01/2018 handle a change in postJump though? Right now this reflects the old logic from ForumsIndexActivity
        //			return;
        //		}
        // TODO: 15/01/2018 a call to display a thread may come before the fragment has been properly created - if so, store the request details and perform it when ready. Handle that here or in #loadThread?
        clearBackStack()
        val threadPage = page ?: FIRST_PAGE
        loadThread(id, threadPage, postJump, true)
    }


    /**
     * Open a specific thread represented in an AwfulURL
     */
    private fun openThread(url: AwfulURL?) {
        // TODO: fix this prefs stuff, get it initialised somewhere consistent in the lifecycle, preferably in AwfulFragment
        // TODO: validate the AwfulURL, e.g. make sure it's the correct type
        if (url == null) {
            Toast.makeText(this.activity, "Error occurred: URL was empty", Toast.LENGTH_LONG).show()
            return
        }
        clearBackStack()
        if (url.isRedirect) {
            startPostRedirect(url.getURL(prefs.postPerPage))
        } else {
            loadThread(url.id.toInt(), url.getPage(prefs.postPerPage).toInt(), url.fragment, true)
        }
    }


    /**
     * Load the thread represented in an AwfulStackEntry
     */
    private fun loadThread(thread: AwfulStackEntry) {
        loadThread(thread.id, thread.page, null, false)
    }


    /**
     * Actually load the new thread
     * @param id        The thread's ID
     * @param page        The number of the page to display
     * @param postJump    An optional URL fragment representing the post ID to jump to
     */
    private fun loadThread(id: Int, page: Int, postJump: String?, fullSync: Boolean) {
        threadId = id
        pageNumber = page
        this.postJump = postJump ?: ""
        setPostFiltering(null, null)
        lastPage = FIRST_PAGE
        updateUiElements()
        showBlankPage()
        if (activity != null) {
            loaderManager.destroyLoader(Constants.THREAD_INFO_LOADER_ID)
            loaderManager.destroyLoader(Constants.POST_LOADER_ID)
            refreshInfo()
            // TODO: shouldn't every load do a sync?
            if (fullSync) {
                syncThread()
            } else {
                refreshPosts()
            }
        }
    }

    private class AwfulStackEntry(val id: Int, val page: Int, val scrollPos: Int)

    private fun pushThread(id: Int, page: Int, postJump: String) {
        if (threadId != 0) {
            backStack.addFirst(AwfulStackEntry(threadId, pageNumber, threadView.scrollY))
        }
        loadThread(id, page, postJump, true)
    }

    private fun popThread() {
        loadThread(backStack.removeFirst())
    }

    private fun clearBackStack() {
        backStack.clear()
    }

    private fun backStackCount(): Int {
        return backStack.size
    }

    override fun onBackPressed(): Boolean {
        return when {
            backStackCount() > 0 -> {
                popThread()
                true
            }
            postFilterUserId != null -> {
                showAllPosts(null)
                true
            }
            else -> false
        }
    }


    override fun doScroll(down: Boolean): Boolean {
        when {
            down -> threadView.pageDown(false)
            else -> threadView.pageUp(false)
        }
        return true
    }


    private fun toggleScreenOn() {
        keepScreenOn = !keepScreenOn
        threadView.keepScreenOn = keepScreenOn

        //TODO icon
        alertView.setTitle(if (keepScreenOn) "Screen stays on" else "Screen turns itself off").show()
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<String>, grantResults: IntArray) {
        when (requestCode) {
            Constants.AWFUL_PERMISSION_WRITE_EXTERNAL_STORAGE -> {
                // If request is cancelled, the result arrays are empty.
                if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) {
                    if (downloadLink != null)
                        enqueueDownload(downloadLink!!)
                } else {
                    Toast.makeText(activity, R.string.no_file_permission_download, Toast.LENGTH_LONG).show()
                }
                downloadLink = null
            }
            else -> super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        }
    }

    companion object {

        private const val THREAD_ID_KEY = "thread_id"
        private const val THREAD_PAGE_KEY = "thread_page"
        private const val SCROLL_POSITION_KEY = "scroll_position"
        private const val sortOrder = AwfulPost.POST_INDEX + " ASC"
        private const val selection = AwfulPost.THREAD_ID + "=? AND " + AwfulPost.POST_INDEX + ">=? AND " + AwfulPost.POST_INDEX + "<?"

        private const val BLANK_USER_ID = 0
        const val FIRST_PAGE = 1
        const val NULL_THREAD_ID = 0
    }
}
