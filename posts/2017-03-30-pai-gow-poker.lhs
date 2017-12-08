---
title: Pai Gow Poker
author: nbloomf
date: 2017-03-30
tags: haskell, games
---

Recently I was in Las Vegas for a conference. While there, I was introduced by a friend to a card game I'd never heard of before called *pai gow poker*. This post is an exploration of the rules and strategy of this strange game. You can get some background on the game from [wikipedia](https://en.wikipedia.org/wiki/Pai_gow_poker).

By the way -- this post is literate Haskell; you can load [the source](https://raw.githubusercontent.com/nbloomf/nbloomf.md/master/posts/2017-03-30-pai-gow-poker.lhs) into GHCi and play along.

In order to build an implementation of pai gow poker in software, we first need a complete and precise list of rules. This turns out to be difficult, because (1) every casino makes minor tweaks to the rules which we expect to affect strategy, and (2) as far as I can tell there is no rule set for the game that does not leave a lot of important questions unanswered. This may be because the poker world assumes a lot of implicit knowledge, but is still unnerving, considering the rules of casino games are frequently codified in [state](http://www.wsgc.wa.gov/activities/game-rules/pai-gow-poker.pdf) [gaming](http://www.doa.state.wi.us/Documents/DOG/Indian%20Gaming/MICS/006%20Pai%20Gow%20Poker%20-%20Text%20Master.doc) commission regulations.

At any rate, here is my best understanding as a non-gambler of the rules for basic pai gow poker.

* **The Players**
    1. The game requires seven players, including the Dealer, seated at table positions numbered 1 to 7. One of the players (possibly the Dealer) is the Banker.
    2. If there are not seven people present to play, the missing players' hands are dealt anyway. These unmanned hands are called *dragon hands*.
    3. The role of Banker alternates between the dealer and the other players in order.
    4. Any player can decline to bank on their turn, in which case the option to bank proceeds to the next player in the sequence.
    5. A player may only act as the Banker if in the previous round they were a non-Banker and they have enough chips to pay out all bets.
* **The Game**
    1. All players place their bets on the table before the cards are dealt.
    2. The dealer shuffles a standard deck with one joker and deals seven cards to each position, whether manned or not. The remaining 4 cards are discarded without being turned over.
    3. All players divide their cards into two hands: one of five cards, and one of two cards.
    4. After these hands are set and placed on the table, all players reveal their hands. The hands cannot be changed from this point forward; any player who touches their cards or chips after this will lose.
    5. Each player then compares their hands against the Banker's, "componentwise". If both hands beat the Banker's respective hands, then the player wins. If both lose, then the player loses. If one hand wins and the other loses, the hand is a *push* and no money changes hands. On individual hands, ties go to the Banker.
    6. The Dealer reconciles all bets against the Banker. The Dealer (i.e. House) takes a commission called the *rake* on all winnings at the table, typically 5%.
* **The Reckoning**
    1. The joker acts as a *bug*. That is, it is an ace, unless it can be used to complete a straight or flush, and in that case it is the highest ranked card which completes the hand.
    2. Five-card hands are ranked using standard poker rules, although some casinos use one exception: the ace-low straight (5432A) ranks below the ace-high straight (AKQJT) and above the king-high straight (KQJT9), rather than as the lowest straight (as in standard rules). I'll call this special case the *ace-low hack*.
    3. Two-card hands are ranked as follows: pairs beat non-pairs, pairs are compared by rank, and non-pairs are compared reverse-lexicographically.
    4. Each player's five-card hand must outrank their two-card hand. That is, if the two-card hand is a pair, the five-card must at least be a pair with greater rank, and if the two-card hand is not a pair, the five-card hand must be at least a high-card hand whose two highest cards outrank the two-card. If this condition is not satisfied the player loses.
    5. The Dealer is required to set her hands according to certain rules, called the *house way*. These depend on the casino hosting the game. Dragon hands are also set using the house way.

Players really only have three choices to make: (1) how much to bet, (2) how to set their cards, and (3) whether or not to bank on their turn. In general there is more than one way to divide a seven-card hand into a five-card and a two-card hand, and due to the win condition it is not obvious to me that one way is strictly better than the others. Obviously the Dealer has the advantage (they always do!) but exactly *how much* of an advantage? To try to answer this, I'll start with some simplifying assumptions.

1. The real game is played with seven players, but from the perspective of a non-banker this is really a two-player game. I'll simulate only two players.
2. Some casinos tack on extra frilly bits. For instance, under some rules players can bet on the dragon hands, or bet on *each other's* hands, or place an "envy" bet that pays in case anyone at the table plays a hand of a given rank. No doubt these change the strategy, but I will ignore this stuff.
3. Exactly how is the joker (the bug) interpreted? Every definition I can find says something like this: **the joker is an ace, unless it can be used to complete a straight or flush, in which case it is the highest-ranked card that completes the hand**. A strict reading of this definition would force the player, in some cases, to play a suboptimal hand. For instance, if the player has 5432 and the joker, then playing the bug as a 6 gives the 6-high straight while playing it as an ace gives the ace-low straight. Without the ace-low hack this forces the player into a suboptimal play, and I suspect this is the reason for the ace-low hack in the first place. As another example, suppose the player has 5678 all of one suit, plus the joker. A strict reading of the bug rule here gives an ambiguous outcome. The joker must be a 9, but of what suit? Certainly this hand should be a straight flush, which ranks higher than a straight, but the bug rule is ambiguous. A better interpretation of the bug would be, I think, that **the joker is either an ace or the card which yields the highest ranking straight or flush**. Because hands are linearly ordered modulo suit, this does away with both the suit ambiguity and the ugly ace-low hack. This is the interpretation of the bug I will use.
4. Exactly how do we compare a five-card hand to a two-card hand? Certainly two pairs or better is better than any two-card hand, so the tricky part is when the five-card hand is a high card or one pair. In these cases we will truncate the five-card hand at the pair or the two highest ranked cards, and compare as two-card hands.

This is my best understanding after reading the "official" rules from several sources including casinos and gaming commissions. But bear in mind that I have never played this game. :)

Now for the code. We start with some imports.

> module PaiGow where
>
> import qualified Data.List                as L
> import qualified Data.Set                 as S
> import qualified Control.Monad.State.Lazy as ST
> import qualified Data.Maybe               as M
> import Control.Monad
> import Control.Monad.Trans.Class (lift)
> import Data.Random (RVar)
> import Data.Random.Extras (choice)
> import Data.RVar (sampleRVar)


The Deck
--------

Pai gow poker is played with a standard French deck plus one joker. We'll model the cards with a few types.

> data Suit
>   -- we impose the usual poker order on suits
>   = Clubs | Diamonds | Hearts | Spades
>   deriving (Show, Eq, Ord, Enum)
> 
> suits :: [Suit]
> suits = [Clubs ..]
> 
> 
> data Rank
>   -- we also impose the aces-high order on ranks
>   = Two   | Three | Four | Five | Six
>   | Seven | Eight | Nine | Ten  | Jack
>   | Queen | King  | Ace
>   deriving (Show, Eq, Ord, Enum)
> 
> ranks :: [Rank]
> ranks = [Two ..]

It will be convenient to distinguish between the "standard" deck of cards and the "full" deck which also includes the joker. So I'll use two card types: ``Carte``, the French word for *card*, will represent the standard cards. ``Card`` will represent either a standard card or a joker.

> data Carte = Carte
>   { rank :: Rank
>   , suit :: Suit
>   } deriving (Show, Eq, Ord)
>
> standardDeck :: [Carte]
> standardDeck = [Carte r s | r <- ranks, s <- suits]
> 
> 
> data Card = Card Carte | Joker
>   deriving (Show, Eq, Ord)
> 
> fullDeck :: [Card]
> fullDeck = (map Card standardDeck) ++ [Joker]

Sanity check:

```haskell
$> length fullDeck
53
```

Note the derived ``Ord`` instance for ``Card``; we've cooked it up so that cards sort on rank and then suit. This will be handy later.

We derived ``Show`` instances for the ``Suit``, ``Rank``, and ``Card`` types to make debugging easier. But it'd also be nice to have a more succinct string representation for cards. We'll use the ``Pretty`` class to represent this.

> class Pretty t where
>   pretty :: t -> String
>
>   -- for convenience
>   prettyIO :: t -> IO ()
>   prettyIO = putStrLn . pretty
> 
> 
> instance (Pretty t) => Pretty (Maybe t) where
>   pretty Nothing  = "*"
>   pretty (Just x) = pretty x
> 
> instance (Pretty t) => Pretty [t] where
>   pretty xs = concat $ L.intersperse " " $ map pretty xs

And Unicode conveniently has characters for playing cards. Woo!

> instance Pretty Carte where
>   pretty (Carte rank suit) = case suit of
>     Clubs    -> get "🃒🃓🃔🃕🃖🃗🃘🃙🃚🃛🃝🃞🃑"
>     Diamonds -> get "🃂🃃🃄🃅🃆🃇🃈🃉🃊🃋🃍🃎🃁"
>     Hearts   -> get "🂲🂳🂴🂵🂶🂷🂸🂹🂺🂻🂽🂾🂱"
>     Spades   -> get "🂢🂣🂤🂥🂦🂧🂨🂩🂪🂫🂭🂮🂡"
>     where
>       get cs =
>         -- pattern match should always succeed
>         let Just c = L.lookup rank $ zip ranks cs
>         in [c]
> 
> instance Pretty Card where
>   pretty (Card c) = pretty c
>   pretty Joker    = "🃏"

For example:

```haskell
$> Carte Two Diamonds
Carte Two Diamonds
$> pretty $ Carte Two Diamonds
"\127170"
$> prettyIO $ Carte Two Diamonds
🃂
```


Detecting Hands
---------------

We have a type representing the cards. Now let's think about dividing groups of seven cards into hands.

First, given a list of five cards, what kind of hand is it?

With the joker present, there are 10 different kinds of five-card poker hands. I had never thought about this before, but when comparing poker hands we mod out the suits. That is, hands that differ only by suit are equivalent. The bottom line is although there are $\binom{53}{5} = 2869685$ different ways to draw 5 cards from the deck, the number of distinct *hands* is much smaller.

Our ``Hand5`` type represents the possible five-card hands. Note that this type does not depend on ``Suit`` at all!

> -- arguments to each constructor must be decreasing
> data Hand5
>   = HighCard Rank Rank Rank Rank Rank
>   | OnePair Pair Kicker Kicker Kicker
>   | TwoPair Pair Pair Kicker
>   | ThreeOfAKind Triplet Kicker Kicker
>   | Straight High
>   | Flush Rank Rank Rank Rank Rank
>   | FullHouse Triplet Pair
>   | FourOfAKind Quad Kicker
>   | StraightFlush High
>   | FiveOfAKind Rank
>   deriving (Eq, Ord, Show)
>
> type Kicker  = Rank
> type Pair    = Rank
> type Triplet = Rank
> type High    = Rank
> type Quad    = Rank

Also the order on hands is graded lexicographic (!) meaning we can derive our ``Ord`` instance. Later on we can compare hands with ``<``. This is what motivated me to tweak the interpretation of the bug -- the order on hands becomes much simpler and we don't need a special case for the ace-low straight.

Now some helper functions.

> -- sort items by count, then by rank
> tally :: (Ord a) => [a] -> [(a, Integer)]
> tally = revlex . count
>   where
>     count :: (Eq a) => [a] -> [(a, Integer)]
>     count [] = []
>     count xs =
>       let
>         x = head xs
>         n = sum $ map (const 1) $ filter (==x) xs
>       in (x,n):(count $ filter (/= x) xs)
> 
>     revlex = L.sortBy $ \(a,h) (b,k) -> if h == k
>       then compare b a
>       else compare k h
>
>
> -- detect if items in a list are sequential
> isSequential :: (Enum a, Eq a) => [a] -> Bool
> isSequential xs = case xs of
>   []  -> True
>   x:_ -> and $ zipWith (==) xs [x ..]
>
>
> -- detect if items in a list are all equal
> allEqual :: (Eq a) => [a] -> Bool
> allEqual list = case list of
>   []   -> True
>   x:xs -> all (== x) xs
>
>
> -- all length k sublists
> choose :: Integer -> [a] -> [[a]]
> choose 0 _  = [[]]
> choose _ [] = []
> choose k (x:xs) = (map (x:) $ choose (k-1) xs) ++ choose k xs
>
>
> -- all length k and n-k cuts
> cuts :: (Eq a) => Integer -> [a] -> [([a],[a])]
> cuts k xs = map (\as -> (as, xs L.\\ as)) $ choose k xs
>
>
> -- while we're at it
> isStraightOrFlush :: Hand5 -> Bool
> isStraightOrFlush (Straight _)      = True
> isStraightOrFlush (Flush _ _ _ _ _) = True
> isStraightOrFlush (StraightFlush _) = True
> isStraightOrFlush _                 = False

To detect a five-card hand we start by tallying the cards by rank. If there are at least two cards of equal rank we have an $N$-of-a-kind, a full house, or two pairs. If all the cards have different ranks we have to check whether or not they all have the same suit and whether or not their ranks are sequential (with a special case for the ace-low straight).

By the way, note how the [partitions](https://en.wikipedia.org/wiki/Partition_%28number_theory%29) of 5 show up in the cases. Neat! Poker hands make way more sense to me now. :)

> toHand5 :: [Carte] -> Hand5
> toHand5 cs = case tally $ map rank cs of
>   [(a,5)] ->              
>     FiveOfAKind a
>
>   [(a,4),(b,1)] ->
>     FourOfAKind a b
>
>   [(a,3),(b,2)] ->
>     FullHouse a b
>
>   [(a,3),(b,1),(c,1)] ->
>     ThreeOfAKind a b c
>
>   [(a,2),(b,2),(c,1)] ->
>     TwoPair a b c
>
>   [(a,2),(b,1),(c,1),(d,1)] ->
>     OnePair a b c d
>
>   [(a,1),(b,1),(c,1),(d,1),(e,1)] ->
>     if allEqual $ map suit cs
>       then if isSequential [e,d,c,b,a]
>         then StraightFlush a
>         else if [a,b,c,d,e] == [Ace,Five,Four,Three,Two]
>           then StraightFlush Five -- the steel wheel
>           else Flush a b c d e
>       else if isSequential [e,d,c,b,a]
>         then Straight a
>         else if [a,b,c,d,e] == [Ace,Five,Four,Three,Two]
>           then Straight Five -- the wheel
>           else HighCard a b c d e
>
>   _ -> error "toHand5: unrecognized hand!"
>
>
> -- compare lists of Cartes as hands
> compareHand5 :: [Carte] -> [Carte] -> Ordering
> compareHand5 as bs = compare (toHand5 as) (toHand5 bs)
>
> -- test lists of Cartes for equality as hands
> equalHand5 :: [Carte] -> [Carte] -> Bool
> equalHand5 as bs = (toHand5 as) == (toHand5 bs)

As a sanity check, let's try to count the hands of each type.

> handType5 :: Hand5 -> String
> handType5 h = case h of
>   HighCard _ _ _ _ _ -> "High Card"
>   OnePair _ _ _ _    -> "One Pair"
>   TwoPair _ _ _      -> "Two Pairs"
>   ThreeOfAKind _ _ _ -> "Three of a Kind"
>   Straight _         -> "Straight"
>   Flush _ _ _ _ _    -> "Flush"
>   FullHouse _ _      -> "Full House"
>   FourOfAKind _ _    -> "Four of a Kind"
>   StraightFlush _    -> "Straight Flush"
>   FiveOfAKind _      -> "Five of a Kind"

This command constructs all possible five-card hands and tallies them by hand type. It runs on my machine in about 4 minutes.

```haskell
$> tally $ map (handType5 . toHand5) $ choose 5 standardDeck
```

And cleaned up, the output matches the number of hands of each type given on [wikipedia](https://en.wikipedia.org/wiki/List_of_poker_hands). This gives some confidence that we're counting hands correctly.

-------------------------
Hand Type        Number
----------       -------
High Card        1302540

One Pair         1098240

Two Pairs        123552

Three of a Kind  54912

Straight         10200

Flush            5108

Full House       3744

Four of a Kind   624

Straight Flush   40
-------------------------

So now we can recognize five-card hands from a standard deck, and detect when one such hand beats another. Let's do the same for two-card hands. There are only two kinds of hands:

> data Hand2
>   = NoPair Rank Rank
>   | YesPair Rank
>   deriving (Eq, Ord, Show)

And detecting them is simpler:

> toHand2 :: [Carte] -> Hand2
> toHand2 cs = case tally $ map rank cs of
>   [(a,2)] ->              
>     YesPair a
>
>   [(a,1),(b,1)] ->
>     NoPair a b
>
>   _ -> error "toHand2: unrecognized hand!"
>
> -- test lists of Cartes for equality as hands
> equalHand2 :: [Carte] -> [Carte] -> Bool
> equalHand2 as bs = (toHand2 as) == (toHand2 bs)

And now to detect when a five-card hand outranks a two-card hand.

> compareFiveToTwo :: Hand5 -> Hand2 -> Ordering
> compareFiveToTwo h5 h2 = case h5 of
>   OnePair a _ _ _ -> case h2 of
>     YesPair b -> compare a b
>     NoPair _ _ -> GT
>   HighCard a b _ _ _ -> case h2 of
>     YesPair _ -> LT
>     NoPair c d -> compare [a,b] [c,d]
>   _ -> GT

A single play consists of a five-card hand and a two-card hand:

> data Play = Play
>   { fiveCard :: [Carte]
>   , twoCard  :: [Carte]
>   }
>
> play :: [Carte] -> [Carte] -> Play
> play a@[_,_,_,_,_] b@[_,_] = Play a b
> play _ _ = error "play: invalid hand!"
>
> instance Pretty Play where
>   pretty (Play five two) = pretty five ++ "   " ++ pretty two
>
>
> equalPlay :: Play -> Play -> Bool
> equalPlay p1 p2 = and
>   [ equalHand5 (fiveCard p1) (fiveCard p2)
>   , equalHand2 (twoCard p1) (twoCard p2)
>   ]
>
> beats :: Play -> Play -> Bool
> beats p1 p2 = and
>   [ (toHand5 $ fiveCard p1) > (toHand5 $ fiveCard p2)
>   , (toHand2 $ twoCard p1)  > (toHand2 $ twoCard p2)
>   ]

So we can classify and compare both five-card and two-card hands consisting of ``Carte``s. But what about the joker? Here's how I will handle that: given seven cards, we will build the list of all possible ways to divide the cards and all valid assignments of the joker. Along the way we can filter out any choices that are beaten by other choices, because they necessarily have a lower probability of winning.

> -- highest ranked valid assignment of the joker (if present)
> mapJoker5 :: [Card] -> [Carte]
> mapJoker5 cs = L.sortBy (flip compare) $ L.maximumBy compareHand5 $ do
>   c <- standardDeck
>   let as = map (to c) cs
>   guard $ (Ace == rank c) || (isStraightOrFlush $ toHand5 as)
>   return as
>   where
>     to :: Carte -> Card -> Carte
>     to c Joker    = c
>     to _ (Card x) = x
>
> -- assign the joker to an ace (if present)
> mapJoker2 :: [Card] -> [Carte]
> mapJoker2 cs = L.sortBy (flip compare) $ case cs of
>   [Card a@(Carte _ _), Card b@(Carte _ _)] -> [a,b]
>   [Card a@(Carte _ s), Joker] -> [a, Carte Ace s]
>   [Joker, Card a@(Carte _ s)] -> [Carte Ace s, a]
>   _ -> error "mapJoker2: unrecognized hand!"
> 
> -- all valid hands
> playChoices :: [Card] -> [Play]
> playChoices cs = L.nubBy equalPlay $ optimal $ do
>   (cs2, cs5) <- cuts 2 cs
>   let (h2, h5) = (mapJoker2 cs2, mapJoker5 cs5)
>   guard $ GT == compareFiveToTwo (toHand5 h5) (toHand2 h2)
>   return $ play h5 h2
>   where
>     -- if one choice is beaten by another, toss it out.
>     optimal (p:ps) = if any (\q -> q`beats`p) ps
>       then optimal ps
>       else p : optimal ps
>     optimal ps = ps

As an example, try this command: it takes the first seven cards from the full deck, divides them into two hands in all 21 possible ways, and pretty prints them.

```haskell
$> sequence_ $ map prettyIO $ playChoices $ take 7 fullDeck
```

To recap: given seven cards, we can construct a list of all the (maximally ranked) valid hands they can form. We can also compare individual hands. We're nearly in a position to simulate the game.

Before we can do that, we need to be able to actually deal the cards!


Randomness
----------

To model a game of pai gow, we need to be able to keep track of a deck and randomly draw cards from it. This is a job for the ``State`` and ``RVar`` monads, which we'll roll into a transformer stack like so.

> type Deal = ST.StateT [Card] RVar

Now an expression of type ``Deal t`` is a computation that keeps a deck as state, may use randomness, and returns a value of type ``t`` when "run". We'll use two helper functions for the "running".

> -- carry out the computation, returning the result.
> runDeal :: Deal t -> IO t
> runDeal x = runDeal' x >>= (return . fst)
>
> -- carry out the computation, returning both the
> -- result and the final state of the deck.
> runDeal' :: Deal t -> IO (t, [Card])
> runDeal' = sampleRVar . ($ fullDeck) . ST.runStateT

For example, here is a computation that attempts to deal a single card.

> drawCard :: Deal (Maybe Card)
> drawCard = do
>   deck <- ST.get -- get the state of the deck
>   case deck of
>     [] -> return Nothing
>     _  -> do
>       c <- lift $ choice deck -- draw a random card
>       ST.put $ L.delete c deck -- remove it from the deck
>       return $ Just c

Now try running the following command a few times.

```haskell
$> runDeal drawCard >>= prettyIO
```

Sequencing a list of ``drawCard``s allows us to draw more than one at a time.

> drawCards :: Integer -> Deal (Maybe [Card])
> drawCards k = do
>   deck <- ST.get -- save the state of the deck
>   draw <- sequence [drawCard | i <- [1..k]]
>   case sequence draw of
>     Just cs -> return $ Just cs -- successful draw
>     Nothing -> do -- ran out of cards!
>       ST.put deck -- return deck to original state
>       return Nothing

Now try running the following command a few times.

```haskell
$> runDeal (drawCards 5) >>= prettyIO
```

This command draws 7 cards from a fresh deck and prints all the best valid pai gow plays they can form. Try running it a few times.

```haskell
$> runDeal (drawCards 7) >>= (sequence_ . map prettyIO . playChoices . M.fromJust)
```


The Game
--------

Finally! We have the parts needed to model a game of pai gow. I'll make one further simplification: each player has a number of plays to choose from, and we will select one at random. This ignores the House Way for the dealer and one of only three choices the players can make, but implementing a complete pai gow AI is beyond the scope of this post. :) I'll be happy getting some concrete win percentages even in this simplified situation.

Each round between the player and the banker has one of three possible outcomes.

> data Outcome = PlayerWin | Push | BankerWin
>   deriving (Eq, Ord, Show)

And the game: first note the asymmetric win conditions for the player and the banker.

> beatsBanker :: Play -> Play -> Bool
> beatsBanker p b = and
>   [ (toHand5 $ fiveCard p) > (toHand5 $ fiveCard b)
>   , (toHand2 $ twoCard p)  > (toHand2 $ twoCard b)
>   ]
>
> beatsPlayer :: Play -> Play -> Bool
> beatsPlayer b p = and
>   [ (toHand5 $ fiveCard b) >= (toHand5 $ fiveCard p)
>   , (toHand2 $ twoCard b)  >= (toHand2 $ twoCard p)
>   ]
>
> -- simulate a round of pai gow
> playPaiGow' :: Deal Outcome
> playPaiGow' = do
>   Just playerHand <- drawCards 7
>   Just bankerHand <- drawCards 7
>   player <- lift $ choice $ playChoices playerHand
>   banker <- lift $ choice $ playChoices bankerHand
>   if player `beatsBanker` banker
>     then return PlayerWin
>     else if banker `beatsPlayer` player
>       then return BankerWin
>       else return Push
> 
> 
> -- simulate k rounds of pai gow
> playRounds' :: Integer -> IO [Outcome]
> playRounds' k = sequence [runDeal playPaiGow' | i <- [1..k]]

Now this command will run 10 rounds of pai gow and tally the results.

```haskell
$> playRounds' 10 >>= (return . tally)
```

I ran the simulation a few times to try to estimate what the win/lose/draw percentages are. It's pretty slow in GHCi, so this took a while! Of course if I ran the simulation again these numbers would be slightly different, but thanks to the [law of large numbers](https://en.wikipedia.org/wiki/Law_of_large_numbers) the percentages converge to their ideal values for this simplified version.

----------------------------------------
Rounds  Banker Win   Push   Player Win
------- -----------  -----  -----------
1000    264          473    263

2000    561          891    548

3000    863          1267   870

4000    1132         1764   1104
----------------------------------------

The first thing I notice is that a plurality of games are pushes. Many sources describe pai gow as a *slow* game, and this is why: many hands are drawn.

With some concrete numbers we can also estimate the expected value of every dollar bet. If $p$ is the probability that the player wins and $q$ the probability they lose, the expected value of 1 dollar bet is $$E = 1.95 \times p + 1 \times (1-p-q) + (-1) \times q = 0.95p - 2q + 1.$$ (Remember the rake!) Using the data from the 3000 round run (which is a very small number) I get $p = 0.29$ and $q = 0.287$, so that $E \approx 0.70$.


Strategy?
---------

Here I simulated a game between two players who follow the rules but otherwise make random choices. I doubt this is the optimal strategy. It might be interesting to see what other strategies are possible, but this post is already too long and I am tired. :)

We can think of a *strategy* here as a mapping ``[Play] -> Deal Play`` that takes a list of possible plays (as given by ``playChoices``) and selects one. ``playPaiGow'`` does this with the strategy ``lift . choice`` for each player (randomly choose one), but by parameterizing on this map we can pass in other strategies.

> type Strategy = [Play] -> Deal Play
>
> -- simulate a round of pai gow
> playPaiGow :: Strategy -> Strategy -> Deal Outcome
> playPaiGow playerStrategy bankerStrategy = do
>   -- normally wouldn't pattern match like this,
>   -- but if this fails something is wrong
>   Just playerHand <- drawCards 7
>   Just bankerHand <- drawCards 7
>   player <- playerStrategy $ playChoices playerHand
>   banker <- bankerStrategy $ playChoices bankerHand
>   if player `beatsBanker` banker
>     then return PlayerWin
>     else if banker `beatsPlayer` player
>       then return BankerWin
>       else return Push
>
> -- choose an optimal hand at random
> randomStrategy :: Strategy
> randomStrategy = lift . choice

Anyway, if you've followed along in GHCi, you can try writing different strategy -- maybe maximize the rank of the five-card hand, or try to favor pushes if no hand beats a majority, or minimize the sum of the ranks of the five-card and two-card hands, or something else. Have fun. :)

> main :: IO ()
> main = putStrLn "ok"
