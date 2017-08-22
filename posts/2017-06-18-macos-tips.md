---
title: macOS Tips
author: nbloomf
date: 2017-06-18
tags: macos
---

I recently started using macOS on a MacBook Pro supplied by my work, after about 10 years of using various flavors of Linux and FreeBSD. So far it's been a little like visiting Canada as a USian; most of the time I recognize the language, and to a first approximation the basic infrastructure is the same. But if you look closely there are some fundamental differences that occasionally come out in ways both subtle and not. :)

This post is a place to dump the little things I learn about how to tweak macOS to my liking. Of course the act of writing them down means I'll be less likely to forget them.

Mission Control
---------------

Manage multiple desktops.

* **``ctrl-up``**: Open Mission Control.
* **``ctrl-left``** and **``ctrl-right``**: Switch among desktops.
* If a window is alone on a desktop, putting it in full screen makes it *really* full screen.
* Split view: to tile two windows on a desktop, click and hold full screen button (green).

Keyboard Shortcuts
------------------

* **``ctrl-F2``**: Move focus to the Menu Bar. (Useful when using full screen or split screen.)
* **``shift-cmd-4``**: Take a screenshot. Change default screenshot folder to ``~/foo`` with the following shell commands.

    ```bash
    defaults write com.apple.screencapture location ~/foo
    killall SystemUIServer
    ```

Finder
------

* Set ``$HOME`` as new window defaut location in Terminal > Preferences.
* **``cmd-shift-.``**: Show/hide hidden files.

Filesystem
----------

* Network shares are mounted to ``/Volumes``

My Favorite Add-ons
-------------------

* [plan9port](https://github.com/9fans/plan9port)
* [xscreensaver](https://www.jwz.org/xscreensaver/)


Bash
----

* ``source ~/.bashrc``: reload ``.bashrc`` in an existing session
