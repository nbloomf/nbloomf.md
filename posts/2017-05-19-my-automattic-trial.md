---
title: My Automattic Trial
author: nbloomf
date: 2017-05-19
tags: automattic
---

This post is about my experience on trial as a Code Wrangler at [Automattic](https://www.automattic.com). During my trial, on days when I was feeling down (and there were a few!) I devoured personal experience posts like this. Maybe reading my story will help someone else. :)

I could write a few different stories about this experience: changing careers, leaving academia, getting into development. But I'll try to focus on what it was like as a trial at Automattic.

Right off the bat, I want to say that Automattic (or A8C as the cool kids say) is an amazing company with a deep commitment to empowering people with open source software. As technology firms go A8C punches well above its weight. With about 550 employees, it manages WordPress.com, shepherds the WordPress.org project (which has countless deployments worldwide), is the .blog registrar, and lots of other things. On top of that A8C is entirely remote.

The company's hiring process is, in a word, *deliberate*, with several layers designed to make sure positions and candidates are well matched. This [article](https://hbr.org/2014/01/hire-by-auditions-not-resumes) by Matt Mullenweg (the CEO) in the Harvard Business Review ([archive](https://web.archive.org/web/20160305122918/https://hbr.org/2014/01/hire-by-auditions-not-resumes)) is a good overview of A8C's hiring philosophy. The short version is that all potential new hires go through an audition called a *trial*. These trials differ in the details, depending on the candidate, the position, and the needs of the company.

In this post I'll tell the story of my own trial, which can be broken into the following phases.

0. The Application,
1. The Initial Interview,
2. The Coding Test,
3. The Trial Project,
4. The Review,
5. The Matt Chat.

This story has a happy ending and I feel like I won the lottery. :)


Prologue
--------

First a little context about me. At the time I applied to A8C, I was working as a math professor at a regional university in the US. Although I'd been a hobbyist programmer and linux user since high school (yay Visual Basic!) and took a little CS in college, I officially majored in math. I got on the academic track, went to grad school to study algebra, and had a couple of visiting professor positions before landing that holy grail of academia -- the Tenure Track job. All along the way I played with code, either for fun or to support my "real" job. First Visual Basic, then C and Java (those CS classes), then Scheme, then Haskell, and Unixy things like AWK and Bash scripting. I wrote programs to supplement my research, and demonstrations for my students, and tools to support my teaching. Because I did this alone, for fun, I had the liberty to choose whatever languages and tools I wanted to use.

A couple of years into my career as a professor I had a realization. I enjoyed the code-writing-and-problem-solving parts of my job way more than I enjoyed the teaching part. For this and other reasons I won't go into here, and after a lot of careful consideration, and with the support of my family, I decided to try to change careers from academia to software development.

So I quit.


The Application
---------------

I couldn't quit my old job immediately -- I've got kids to feed. So it'd be better to say I decided to look for another job. In hindsight this made no sense at all! I had no professional experience and my formal training is *at best* tangential to anything tech related. And of course having spent my entire adult life in academia I had no idea how to find a real job.

I knew a couple of people in the industry, so I reached out to them for advice on how to make myself a good candidate. I was surprised when one of them encouraged me to apply at his company -- a place I had only vaguely heard of called Automattic (with two *t*s!) After agonizing for weeks, and with lots of encouragement from my partner, I sent in an application. (One page, typeset in LaTeX.) I also polished up some programming projects on GitHub that I could point to. I CC'd my friend on the application (at his suggestion) and waited. This was in June/July 2016. It was one of several places I sent resumes to.

Job titles at A8C are... idiosyncratic, for good reason. At the time I applied there were openings for several different developer-type positions. One, the "Code Wrangler", had a vague enough description that my background could honestly be shoehorned into relevance. :) So that's the one I applied to.

This is a good place to mention that I've gotten pretty good at being rejected. I sent painstakingly individualized applications to 135 teaching jobs (who's counting?) before I landed the job I am now leaving. Most of my research article submissions are rejected. Even my thesis advisor doesn't like me very much. :) So I was fully expecting not to hear back from A8C at all.

But I did!

(I have since learned that A8C tries really hard to get in touch with every applicant. This is a classy move and in my experience *not* the norm.) About a month after sending in a resume by email, I was invited to a first interview.

I was cautiously optimistic.


The Initial Interview
---------------------

My first interview was with a hiring engineer via Slack. The cool kids probably all know this, but I didn't -- Slack is like a souped-up IRC that lots of organizations use for internal communication. For an all-remote company like A8C internal communication is absolutely crucial, and they take it seriously -- Slack is just one of several tools teams at A8C use daily. And so it makes sense that the first interview would take place using the same medium that the company uses for day-to-day communication. Note that Slack is primarily a text-based tool -- it was several months into the trial before anyone at A8C heard the sound of my voice or even saw my face.

My interviewer and I happened to be about 9 time zones apart, so the closest we could get to overlapping work hours was something like 4pm his time and 7am my time. But it worked! Next lesson: "all remote" really means "all remote"!

Anyway, the first interview was pretty straightforward; mostly questions about how I came to apply and some technical questions about projects I'd worked on. (It was handy to be able to paste links to GitHub for this part.) There were no CS trivia or fizz-buzz type questions, as I had come to assume were standard for tech interviews, although that might have been different if I didn't have code samples to show. I was nervous the whole time, but also excited. After about an hour my interviewer said he felt comfortable moving me to the next phase.


The Coding Test
---------------

After the initial interview I moved on to the Coding Test. I got a link to a svn repository containing a WordPress plugin with instructions to add a particular feature and -- paraphrasing here -- "make any other changes you think are necessary". :) This project came with a rough deadline of one week.

So to make progress on this goal, we have to (1) get a local installation of WordPress and (2) edit/refactor/write the actual PHP according to WP style. I have to confess that I'd never done either of these things before starting the trial! So my first day of working on the test was spent just getting a development environment up and running. My interviewer gave me some very good tips on how to get started, and I learned a ton along the way. I kept notes which you can read [elsewhere](/posts/2016-12-30-hacking-wordpress-getting-started.html) on this blog.

The commit history in the test repo tells the story. My edits started out very small and timid as I got used to the workflow, then grew as I came to understand the code, how I wanted to refactor it, and how to achieve my goals in PHP. Towards the end I got a little distracted and added some extra frilly bits and edited the documentation. But after about 5 days I called it done and reported back to the interviewer.

Again, he was comfortable enough with my work to move me on to the next phase. At this point I was passed on to another hiring engineer who would oversee my trial project.


The Trial Project
-----------------

A few weeks after the coding test I started the trial project proper. This was at the beginning of October 2016.

At A8C, the trial project is an audition -- you do the work you'd be doing as an employee. For Code Wrangler positions that means working on a reasonably sized new feature, refactor, or whatever else may be appropriate. The specific project is chosen by the hiring engineer, probably (I guess) with input from whatever team the trial will be working with. The goal is to let the trialmattician (as they're called) show how they approach problems, ask for help, make progress, document their work -- you know, the kinds of tasks one actually does day-to-day. But at the same time, the project is ideally one that can eventually be deployed to production. Since so much of A8C's code is open source, the mechanics of working with and contributing to the code is pretty straightforward.

Anyway, my trial project was set up as contract work. I understand that this is standard for all A8C trials from party planners to CFOs. So I was paid (a flat, non-negotiable rate) for my work. This was the first time I was paid to write code, which felt really good. I told myself that, at this point, even if I didn't move past the trial project I would be able to put "Contractor at Automattic" on my CV. :) Before starting the trial I also had to read and sign some documents. There was the contract agreement itself, but also some things about transfer of copyright and conflict of interest. I read these carefully and didn't see anything unreasonable.

My specific project was to remove some unnecessary restrictions on a feature of an important WordPress plugin called Jetpack. The details are not super important here, but that work was mostly done in public and you can see the final pull request on GitHub [here](https://github.com/automattic/jetpack/pull/5503). I was new to PHP, so I had to learn a lot of details. Frankly, I started by imagining how I'd structure the code if I could use Haskell, and then did that in PHP. Functional programming for the win!

I did a lot of research. In fact for the first week I wrote no code at all, and instead just read as much relevant material as I could find -- RFCs, standards documents, mailing list and message board threads about best practices, estimates on realistic data, and more. I also kept lots of notes about design along the way. These notes morphed into the internal documentation for the code.

An engineer from the team was assigned to review my progress, and I always felt comfortable asking questions in the team Slack channel when I got really stuck.

This part of the trial lasted for about 14 weeks. Everything I read about trials said they were usually 4--6 weeks, so I was pretty nervous as 2016 turned into 2017. But, working on the project during evenings and weekends I was making steady progress. I think the hiring engineers got swamped with trials -- the company was growing pretty fast at the time -- and mine just got stretched out, maybe because I let the team know up front that my teaching contract was through May 2017. At any rate, the extended period was probably for the best; in my biased opinion my code got **a lot** better in the second half of the trial period as I got more familiar with PHP (in general) and WordPress-flavored PHP (in particular).

After about 3 months the team reported up the chain that my project was done for the purpose of the trial. But it wasn't quite ready to be merged in. After a few more weeks' worth of polishing it did eventually get merged to the development branch, although as of this writing there are still some bugs being worked out. It turns out that deploying to millions of websites will expose flaws in even the most carefully written code!

In the end, my pull request was about 7000 lines of new code and comments (including unit tests). I also wrote a bunch of documentation.


The Review
----------

The next step was a one-on-one review with the hiring engineer (the one that oversaw my trial, not the one that did my initial interview). This was a video chat and the first time anyone at A8C saw what I look like (other than my friend on the inside, who wasn't involved in my trial). This lasted about an hour. I could tell that the interviewer had read my code very carefully. He asked very detailed questions about its structure, what it did, why I did things certain ways, and so on. He also made some suggestions for edits. I recall that one was a blocking change (that wasn't too hard to make because of how the code was structured) and several more had to do with quirks of PHP that I wasn't aware of.

At the end of the interview I got instructions for how to proceed to the Matt Chat.


The Matt Chat
-------------

Matt Mullenweg is cofounder, CEO, and president of Automattic, Inc., and he personally interviews every candidate who makes it through the trial. This is the last step in the screening process, called the *Matt Chat*. I've also heard this referred to as the *sorting Matt*, since one purpose of the chat is to help determine where in the company a candidate would best fit.

My Matt Chat took place in Slack. It took several hours from start to finish, although that was mostly because I had some previously scheduled commitments in the middle. One does not know in advance exactly when one's Matt Chat will happen, and so one must be prepared! Fortunately Matt was OK with having an asynchronous chat. This time the questions were more about me, how I work, how I deal with different situations, and so on. Matt's a really interesting guy and I tried not to be wigged out chatting with the CEO of a billion dollar company. :)

Toward the end Matt made an informal offer, which was followed by a formal offer via email. This was on a Friday afternoon. There was no way I was going to turn it down but I try to sleep on every contract I sign, especially one that completely changes my family's life. :) So I waited until the following Monday to formally accept.

The company was super cool about working around my teaching contract -- because of that, there was about a 4 month gap between when I accepted the offer and my first day at A8C. Every day for those four months I've been on cloud nine.


Timeline
--------

Here's an approximate calendar of the whole process from "application sent" to "first day on the job", reconstructed from email and Slack logs.

-------------------------------------
Date        Event
-----       ------
2016-06-30  Emailed resume.

2016-08-05  First contact! Scheduled the first interview with a hiring engineer.

2016-08-11  Initial interview, conducted in Slack. Received instructions for a
            short coding test in PHP.

2016-08-16  Finished the coding test.

2016-10-01  Start the trial project. Type type type. :)

2017-01-??  "Finished" the trial project.

2017-02-10  Had the Matt Chat and received a formal job offer! This was a Friday.

2017-02-13  Formally accepted the offer! This was the following Monday; I took
            the weekend to think because this move is such a big one.

2017-03-13  Met with my new teammates at the Merchant Risk Council conference.

2017-06-05  First official day on the job! The big delay here was so I could
            finish out my contract at my old job.
-------------------------------------

By the way, [we're hiring](https://automattic.com/work-with-us/)!
