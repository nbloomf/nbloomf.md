---
title: Hacking on WordPress: Getting Started
author: nbloomf
date: 2016-12-30
tags: wordpress
---

This post is about how to set up a local [WordPress](https://www.wordpress.org) development environment. There are probably better posts by more qualified authors out there, but this one is mine. :)

For the last few months I've been playing around with the guts of WordPress (more specifically, the [Jetpack](https://jetpack.com/) plugin). I have had a blog at WP.com for several years but I'd never tried my hand at building plugins.

When I started I had no experience with PHP, or development in a dynamic language, or any kind of modern best practice, really. So this post summarizes everything I had to figure out to go from zero to one.

I'm using Ubuntu, so watch out if you're following along on a different OS.


## Virtual Machines

To use WordPress you have to install it on a computer first, right? Of course. Presumably then if you want to use WordPress the most natural thing to do is install it on your computer.

No!

The trouble with installing software on your computer is that it can get tricky if you want *more than one version at a time*, or if *something goes horribly wrong* (which happens a lot), or lord help you if *the software is in constant flux*.

Instead we can create a *virtual machine* and install WordPress on that. This has several advantages over installing WordPress directly. Virtual machines can be created and destroyed at will, so we can tinker without fear. Virtual machines are also (more easily) reproducible, so if we trash one we can make a new one just like it. And virtual machines are (more easily) configurable, so we can use one with exactly the versions of any packages we want. And of course the biggest advantage is that I can have lots of different virtual machines, but I've only got one real machine.

I'll use "local machine" to refer to my real, actual, physical computer, as opposed to a virtual machine or VM.

Good news: the fine people of the community have put together a few different virtual machines specifically for hacking on WordPress. After installing some infrastructure on your local machine, these are ready to go with a ``git clone``.

1. [VVV](https://github.com/Varying-Vagrant-Vagrants/VVV): Includes almost everything you could want. Getting started is more involved.
2. [Chassis](http://docs.chassis.io/en/latest/): Easy to get started. Includes less stuff out of the box, but easily extended.

Both VVV and Chassis are built on top of VirtualBox and Vagrant and both have great documentation for how to install and get started. I used both because some things were easier to do with VVV (like running unit tests) and others easier with Chassis. But that was just my experience.

Once you have one of these VMs set up there are some useful commands (all called from the root VM directory on your local machine). Roughly in order of most to least used:

1. ``vagrant up``: this "turns on" the machine.
2. ``vagrant ssh``: this logs you into the machine so you can muck around.
3. ``vagrant halt``: this "turns off" the machine.
4. ``vagrant provision``: only used if you change the configuration settings of a VM.

Beware that getting a VM set up may be fiddly and take a while, especially the first time! But your patience will be rewarded.

Once a VM is up and running, and assuming that everything went OK, you can then browse to your shiny new WordPress installation at ``local.wordpress.dev`` (VVV) or ``vagrant.local`` (Chassis). The actual WP files on the VM are cloned from your local machine, so you can edit locally and have your changes visible immediately. For example, here's an example workflow with Chassis.

1. (First time only) Clone Chassis to the directory ``$FOO`` on my local machine.
2. Say ``vagrant up`` in ``$FOO`` (and wait while the machine boots)
3. Open ``vagrant.local/$BAR`` in my browser, login with ``admin`` and ``password`` if needed
4. Edit my plugin in ``$FOO/content/plugins/``
5. Refresh ``vagrant.local/$BAR`` in the browser to see changes
6. Repeat 4--5 until I'm happy
7. ``git commit`` my changes


## Where Stuff Goes

Okay so this is going to sound silly to experienced WP people, but plugins go in the ``www/wordpress-default/wp-content/plugins`` (VVV) or ``content/plugins`` (Chassis) directory. I know, right! But I was confused about that for way too long. :)

Another important file is ``wp-config.php``. This is where you can put little local customizations for your WP install. For instance, during development you will probably want to add these two lines to this file:

```php
define( 'WP_DEBUG', true );
define( 'WP_DEBUG_LOG', true );
```

These enable error logging (the error log lives in the content directory, up one level from the plugin directory).

If you're working on Jetpack, you'll also need this line (otherwise nothing works):

```php
define( 'JETPACK_DEV_DEBUG', true );
```


## Style

WordPress is huuuuge. To help contain the chaos there is an official [style guide](https://codex.wordpress.org/WordPress_Coding_Standards). And so we don't have to remember all the standards there is a nice tool, ``phpcs``, that can automatically check your PHP code for bad style. To use it:

1. Install [PHP CodeSniffer](https://github.com/squizlabs/PHP_CodeSniffer) on your local machine.
2. Install the official [WordPress codesniffer rules](https://github.com/WordPress-Coding-Standards/WordPress-Coding-Standards).
3. To sniff the file ``foo.php``, navigate to it in the terminal on your local machine and run ``phpcs --standard=WordPress foo.php``

Supposedly this can integrate with IDEs, but I don't know anything about that.


## Databases

There's this great tool, MySQL Workbench, that we can use to browse the database of our WordPress installation in Chassis. The [documentation](https://github.com/Chassis/Chassis/wiki/Connecting-to-MySQL) is pretty straightforward. This is **really useful** if your plugin messes with the database -- you can run queries, see the results, delete tables, and probably more stuff too.


## Unit Testing

I never did figure out how to run the entire WordPress unit test suite myself; there was some kind of naming conflict that was beyond my ability to fix. (That may have been fixed by the time you, dear reader, try this.) But I did figure out how to run individual test files, which was good enough.

I ran the unit tests from inside a VVV virtual machine. The tool that runs the tests is called ``phpunit``, and is very picky about where you ask it to do things. For example, I was working with the [Jetpack](https://jetpack.com/) plugin, and wanted to run unit tests for it. To do this, I first installed Jetpack to ``wordpress-develop`` (this is important). Then I navigated to 

```bash
vagrant@vvv:/vagrant/www/wordpress-develop/src/wp-content/plugins/jetpack
```

*in the virtual machine* and said

```bash
phpunit tests/php/$PATH_TO_TEST_MODULE
```

to actually run the tests.

The easiest way to write new unit tests is to copy and edit an existing test. Check out the standard list of [PHPUnit assertion types](https://phpunit.de/manual/current/en/appendixes.assertions.html).


## Email

If your plugin needs to send email, you can test this without actually sending mail by using mailcatcher (comes with VVV) or [MailHog](https://github.com/Chassis/MailHog) (Chassis extension).


## WordPress from the Command Line

This is less immediately useful, but still handy: you can interact with a WP install from the command line with [wp-cli](http://wp-cli.org/). This comes with VVV. To use it, first SSH to the virtual machine and then invoke ``wp`` from within ``/srv/www/wordpress-default`` (or whatever install you're using).

Most interactions with the WP interface can be scripted with ``wp-cli``.


## Generating a Fake Blog

Depending on what kind of plugin you're building, you may need to have a blog that's actually populated with posts and comments. One easy way to generate a dummy blog is with the [FakerPress](https://wordpress.org/plugins/fakerpress/) plugin. This can be installed and used from within WP; it's pretty straightforward. But FakerPress was also super slow on my machine.

Another option for getting dummy blog data is to generate a [WXR](https://devtidbits.com/2011/03/16/the-wordpress-extended-rss-wxr-exportimport-xml-document-format-decoded-and-explained/) file and import it, either through the WP interface or on the command line with ``wp-cli``. I was able to do this successfully (I even made a [little tool](https://github.com/nbloomf/prattle) for generating WXR archives) but it is less straightforward because as far as I can tell the only documentation for the WXR format is "whatever WordPress exports".


## Measuring Performance

There's a few ways to measure WordPress' performance.

1. VVV comes with [several tools](https://github.com/Varying-Vagrant-Vagrants/VVV/wiki/Code-Debugging). xDebug and Cachegrind are nice; with these enabled you can append ``?XDEBUG_PROFILE`` to any query to get a nice profile log with webgrind.
2. The [Query Monitor](https://wordpress.org/plugins/query-monitor/) plugin is nice for measuring database performance.
3. As a last resort you can measure the end-to-end performance of a site using ``curl``. For example, here's a pipeline that gets the average time-to-first-byte of 200 requests to ``$URL``. (When editing locally this time is dominated by the site itself.)

    ```bash
    for i in {1..200}; do \
      curl -s -w "%{time_starttransfer}\n" -o /dev/null $URL; \
    done \
      | awk '{ sum += $1; n++ } END { if (n > 0) print "average of " n " requests: " sum / n; }'
    ```
