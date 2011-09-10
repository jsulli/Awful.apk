$(document).ready(function() {
    var clear = function() {
        $("#thread-body").html("");
    };

    $('.action-button').live('click', function(event) {
        if ($(this).hasClass("editable")) {
            listener.onEditablePostClick($(this).attr('id'), $(this).attr('lastreadurl'));
        } else {
            listener.onPostClick($(this).attr('id'), $(this).attr('lastreadurl'));
        }
    });

    var posts = JSON.parse(post_list);
    var prefs = JSON.parse(preferences);
    var page = JSON.parse(pager);

    var thread = $("#thread-body");
    var light = true;

    for (var i = 0; i < posts.length; i++) {
        current = JSON.parse(posts[i]);

        var background;

        if (current.isOp == "true") {
            background = prefs.OPColor;
        } else if (current.previouslyRead == "true") {
            background = light ? prefs.readBackgroundColor : prefs.readBackgroundColor2;
        } else {
            background = light ? prefs.backgroundColor : prefs.backgroundColor2;
        }

        light = !light;

        var post_data = {
            postId: current.id,
            username: current.username,
            postdate: current.date,
            avatar: current.avatar,
            content: current.content,
            background: background,
            lastread: (current.previouslyRead == "true") ? "read" : "unread",
            lastreadurl: current.lastReadUrl,
            editable: (current.editable == "true") ? "editable" : "noneditable",
            fontColor: prefs.fontColor,
            fontSize: prefs.fontSize,
        };

        thread.append(ich.post(post_data));
    }

    $('.content').append(ich.pagefooter({
        currentPage: page.currentPage,
        pageTotal: page.pageTotal,
        nextPageButton: (page.isLastPage == "true") ? "stat_notify_sync.png" : "r_arrow.png",
    }));

    $('#previous-page').bind('click', function(event) {
        clear();
        listener.onPreviousPageClick();
    });

    if (page.isLastPage == "false") {
        $('#next-page').bind('click', function(event) {
            clear();
            listener.onNextPageClick();
        });
    } else {
        $('#next-page').bind('click', function(event) {
            clear();
            listener.onRefreshPageClick();
        });
    }

    var salr = new SALR(prefs);

    $(window).scrollTop($('.unread').first().offset().top);
});

$(window).load(function() {
    $(window).scrollTop($('.unread').first().offset().top);
});
