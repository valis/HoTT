{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Parser.ParGrammar where
import Parser.AbsGrammar
import Parser.LexGrammar
import Parser.ErrM

-- parser produced by Happy Version 1.18.10

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 (Integer)
	| HappyAbsSyn5 (U)
	| HappyAbsSyn6 (PIdent)
	| HappyAbsSyn7 (Defs)
	| HappyAbsSyn8 (Def)
	| HappyAbsSyn9 ([Def])
	| HappyAbsSyn10 (Expr)
	| HappyAbsSyn16 (Arg)
	| HappyAbsSyn17 ([Arg])
	| HappyAbsSyn18 (Binder)
	| HappyAbsSyn19 ([Binder])
	| HappyAbsSyn20 (TypedVar)
	| HappyAbsSyn21 ([TypedVar])

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62 :: () => Int -> ({-HappyReduction (Err) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_1,
 happyReduce_2,
 happyReduce_3,
 happyReduce_4,
 happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38 :: () => ({-HappyReduction (Err) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

action_0 (36) = happyShift action_7
action_0 (6) = happyGoto action_3
action_0 (7) = happyGoto action_4
action_0 (8) = happyGoto action_5
action_0 (9) = happyGoto action_6
action_0 _ = happyReduce_7

action_1 (34) = happyShift action_2
action_1 _ = happyFail

action_2 _ = happyReduce_1

action_3 (26) = happyShift action_10
action_3 (17) = happyGoto action_9
action_3 _ = happyReduce_31

action_4 (38) = happyAccept
action_4 _ = happyFail

action_5 (27) = happyShift action_8
action_5 _ = happyReduce_8

action_6 _ = happyReduce_4

action_7 _ = happyReduce_3

action_8 (36) = happyShift action_7
action_8 (6) = happyGoto action_3
action_8 (8) = happyGoto action_5
action_8 (9) = happyGoto action_32
action_8 _ = happyReduce_7

action_9 (28) = happyShift action_31
action_9 (32) = happyShift action_27
action_9 (36) = happyShift action_7
action_9 (6) = happyGoto action_13
action_9 (16) = happyGoto action_30
action_9 _ = happyFail

action_10 (22) = happyShift action_23
action_10 (29) = happyShift action_24
action_10 (30) = happyShift action_25
action_10 (31) = happyShift action_26
action_10 (32) = happyShift action_27
action_10 (33) = happyShift action_28
action_10 (34) = happyShift action_2
action_10 (35) = happyShift action_29
action_10 (36) = happyShift action_7
action_10 (4) = happyGoto action_11
action_10 (5) = happyGoto action_12
action_10 (6) = happyGoto action_13
action_10 (10) = happyGoto action_14
action_10 (11) = happyGoto action_15
action_10 (12) = happyGoto action_16
action_10 (13) = happyGoto action_17
action_10 (14) = happyGoto action_18
action_10 (15) = happyGoto action_19
action_10 (16) = happyGoto action_20
action_10 (20) = happyGoto action_21
action_10 (21) = happyGoto action_22
action_10 _ = happyFail

action_11 _ = happyReduce_26

action_12 _ = happyReduce_27

action_13 _ = happyReduce_29

action_14 _ = happyReduce_6

action_15 _ = happyReduce_11

action_16 _ = happyReduce_14

action_17 (24) = happyShift action_45
action_17 (25) = happyShift action_46
action_17 _ = happyReduce_17

action_18 (22) = happyShift action_43
action_18 (28) = happyShift action_44
action_18 (29) = happyShift action_24
action_18 (30) = happyShift action_25
action_18 (32) = happyShift action_27
action_18 (33) = happyShift action_28
action_18 (34) = happyShift action_2
action_18 (35) = happyShift action_29
action_18 (36) = happyShift action_7
action_18 (4) = happyGoto action_11
action_18 (5) = happyGoto action_12
action_18 (6) = happyGoto action_13
action_18 (15) = happyGoto action_42
action_18 (16) = happyGoto action_20
action_18 _ = happyReduce_19

action_19 _ = happyReduce_21

action_20 _ = happyReduce_22

action_21 (22) = happyShift action_41
action_21 (20) = happyGoto action_21
action_21 (21) = happyGoto action_40
action_21 _ = happyReduce_37

action_22 (24) = happyShift action_38
action_22 (25) = happyShift action_39
action_22 _ = happyFail

action_23 (22) = happyShift action_23
action_23 (29) = happyShift action_24
action_23 (30) = happyShift action_25
action_23 (31) = happyShift action_26
action_23 (32) = happyShift action_27
action_23 (33) = happyShift action_28
action_23 (34) = happyShift action_2
action_23 (35) = happyShift action_29
action_23 (36) = happyShift action_7
action_23 (4) = happyGoto action_11
action_23 (5) = happyGoto action_12
action_23 (6) = happyGoto action_13
action_23 (10) = happyGoto action_37
action_23 (11) = happyGoto action_15
action_23 (12) = happyGoto action_16
action_23 (13) = happyGoto action_17
action_23 (14) = happyGoto action_18
action_23 (15) = happyGoto action_19
action_23 (16) = happyGoto action_20
action_23 (20) = happyGoto action_21
action_23 (21) = happyGoto action_22
action_23 _ = happyFail

action_24 _ = happyReduce_23

action_25 _ = happyReduce_25

action_26 (32) = happyShift action_27
action_26 (36) = happyShift action_7
action_26 (6) = happyGoto action_13
action_26 (16) = happyGoto action_34
action_26 (18) = happyGoto action_35
action_26 (19) = happyGoto action_36
action_26 _ = happyFail

action_27 _ = happyReduce_30

action_28 _ = happyReduce_24

action_29 _ = happyReduce_2

action_30 _ = happyReduce_32

action_31 (22) = happyShift action_23
action_31 (29) = happyShift action_24
action_31 (30) = happyShift action_25
action_31 (31) = happyShift action_26
action_31 (32) = happyShift action_27
action_31 (33) = happyShift action_28
action_31 (34) = happyShift action_2
action_31 (35) = happyShift action_29
action_31 (36) = happyShift action_7
action_31 (4) = happyGoto action_11
action_31 (5) = happyGoto action_12
action_31 (6) = happyGoto action_13
action_31 (10) = happyGoto action_33
action_31 (11) = happyGoto action_15
action_31 (12) = happyGoto action_16
action_31 (13) = happyGoto action_17
action_31 (14) = happyGoto action_18
action_31 (15) = happyGoto action_19
action_31 (16) = happyGoto action_20
action_31 (20) = happyGoto action_21
action_31 (21) = happyGoto action_22
action_31 _ = happyFail

action_32 _ = happyReduce_9

action_33 _ = happyReduce_5

action_34 _ = happyReduce_33

action_35 (32) = happyShift action_27
action_35 (36) = happyShift action_7
action_35 (6) = happyGoto action_13
action_35 (16) = happyGoto action_34
action_35 (18) = happyGoto action_35
action_35 (19) = happyGoto action_59
action_35 _ = happyReduce_34

action_36 (25) = happyShift action_58
action_36 _ = happyFail

action_37 (23) = happyShift action_56
action_37 (26) = happyShift action_57
action_37 _ = happyFail

action_38 (22) = happyShift action_23
action_38 (29) = happyShift action_24
action_38 (30) = happyShift action_25
action_38 (32) = happyShift action_27
action_38 (33) = happyShift action_28
action_38 (34) = happyShift action_2
action_38 (35) = happyShift action_29
action_38 (36) = happyShift action_7
action_38 (4) = happyGoto action_11
action_38 (5) = happyGoto action_12
action_38 (6) = happyGoto action_13
action_38 (12) = happyGoto action_55
action_38 (13) = happyGoto action_49
action_38 (14) = happyGoto action_18
action_38 (15) = happyGoto action_19
action_38 (16) = happyGoto action_20
action_38 (20) = happyGoto action_21
action_38 (21) = happyGoto action_50
action_38 _ = happyFail

action_39 (22) = happyShift action_23
action_39 (29) = happyShift action_24
action_39 (30) = happyShift action_25
action_39 (32) = happyShift action_27
action_39 (33) = happyShift action_28
action_39 (34) = happyShift action_2
action_39 (35) = happyShift action_29
action_39 (36) = happyShift action_7
action_39 (4) = happyGoto action_11
action_39 (5) = happyGoto action_12
action_39 (6) = happyGoto action_13
action_39 (11) = happyGoto action_54
action_39 (12) = happyGoto action_16
action_39 (13) = happyGoto action_17
action_39 (14) = happyGoto action_18
action_39 (15) = happyGoto action_19
action_39 (16) = happyGoto action_20
action_39 (20) = happyGoto action_21
action_39 (21) = happyGoto action_22
action_39 _ = happyFail

action_40 _ = happyReduce_38

action_41 (22) = happyShift action_23
action_41 (29) = happyShift action_24
action_41 (30) = happyShift action_25
action_41 (31) = happyShift action_26
action_41 (32) = happyShift action_27
action_41 (33) = happyShift action_28
action_41 (34) = happyShift action_2
action_41 (35) = happyShift action_29
action_41 (36) = happyShift action_7
action_41 (4) = happyGoto action_11
action_41 (5) = happyGoto action_12
action_41 (6) = happyGoto action_13
action_41 (10) = happyGoto action_53
action_41 (11) = happyGoto action_15
action_41 (12) = happyGoto action_16
action_41 (13) = happyGoto action_17
action_41 (14) = happyGoto action_18
action_41 (15) = happyGoto action_19
action_41 (16) = happyGoto action_20
action_41 (20) = happyGoto action_21
action_41 (21) = happyGoto action_22
action_41 _ = happyFail

action_42 _ = happyReduce_20

action_43 (22) = happyShift action_23
action_43 (29) = happyShift action_24
action_43 (30) = happyShift action_25
action_43 (31) = happyShift action_26
action_43 (32) = happyShift action_27
action_43 (33) = happyShift action_28
action_43 (34) = happyShift action_2
action_43 (35) = happyShift action_29
action_43 (36) = happyShift action_7
action_43 (4) = happyGoto action_11
action_43 (5) = happyGoto action_12
action_43 (6) = happyGoto action_13
action_43 (10) = happyGoto action_52
action_43 (11) = happyGoto action_15
action_43 (12) = happyGoto action_16
action_43 (13) = happyGoto action_17
action_43 (14) = happyGoto action_18
action_43 (15) = happyGoto action_19
action_43 (16) = happyGoto action_20
action_43 (20) = happyGoto action_21
action_43 (21) = happyGoto action_22
action_43 _ = happyFail

action_44 (22) = happyShift action_43
action_44 (29) = happyShift action_24
action_44 (30) = happyShift action_25
action_44 (32) = happyShift action_27
action_44 (33) = happyShift action_28
action_44 (34) = happyShift action_2
action_44 (35) = happyShift action_29
action_44 (36) = happyShift action_7
action_44 (4) = happyGoto action_11
action_44 (5) = happyGoto action_12
action_44 (6) = happyGoto action_13
action_44 (14) = happyGoto action_51
action_44 (15) = happyGoto action_19
action_44 (16) = happyGoto action_20
action_44 _ = happyFail

action_45 (22) = happyShift action_23
action_45 (29) = happyShift action_24
action_45 (30) = happyShift action_25
action_45 (32) = happyShift action_27
action_45 (33) = happyShift action_28
action_45 (34) = happyShift action_2
action_45 (35) = happyShift action_29
action_45 (36) = happyShift action_7
action_45 (4) = happyGoto action_11
action_45 (5) = happyGoto action_12
action_45 (6) = happyGoto action_13
action_45 (12) = happyGoto action_48
action_45 (13) = happyGoto action_49
action_45 (14) = happyGoto action_18
action_45 (15) = happyGoto action_19
action_45 (16) = happyGoto action_20
action_45 (20) = happyGoto action_21
action_45 (21) = happyGoto action_50
action_45 _ = happyFail

action_46 (22) = happyShift action_23
action_46 (29) = happyShift action_24
action_46 (30) = happyShift action_25
action_46 (32) = happyShift action_27
action_46 (33) = happyShift action_28
action_46 (34) = happyShift action_2
action_46 (35) = happyShift action_29
action_46 (36) = happyShift action_7
action_46 (4) = happyGoto action_11
action_46 (5) = happyGoto action_12
action_46 (6) = happyGoto action_13
action_46 (11) = happyGoto action_47
action_46 (12) = happyGoto action_16
action_46 (13) = happyGoto action_17
action_46 (14) = happyGoto action_18
action_46 (15) = happyGoto action_19
action_46 (16) = happyGoto action_20
action_46 (20) = happyGoto action_21
action_46 (21) = happyGoto action_22
action_46 _ = happyFail

action_47 _ = happyReduce_12

action_48 _ = happyReduce_15

action_49 (24) = happyShift action_45
action_49 _ = happyReduce_17

action_50 (24) = happyShift action_38
action_50 _ = happyFail

action_51 (22) = happyShift action_43
action_51 (29) = happyShift action_24
action_51 (30) = happyShift action_25
action_51 (32) = happyShift action_27
action_51 (33) = happyShift action_28
action_51 (34) = happyShift action_2
action_51 (35) = happyShift action_29
action_51 (36) = happyShift action_7
action_51 (4) = happyGoto action_11
action_51 (5) = happyGoto action_12
action_51 (6) = happyGoto action_13
action_51 (15) = happyGoto action_42
action_51 (16) = happyGoto action_20
action_51 _ = happyReduce_18

action_52 (23) = happyShift action_56
action_52 _ = happyFail

action_53 (26) = happyShift action_57
action_53 _ = happyFail

action_54 _ = happyReduce_13

action_55 _ = happyReduce_16

action_56 _ = happyReduce_28

action_57 (22) = happyShift action_23
action_57 (29) = happyShift action_24
action_57 (30) = happyShift action_25
action_57 (31) = happyShift action_26
action_57 (32) = happyShift action_27
action_57 (33) = happyShift action_28
action_57 (34) = happyShift action_2
action_57 (35) = happyShift action_29
action_57 (36) = happyShift action_7
action_57 (4) = happyGoto action_11
action_57 (5) = happyGoto action_12
action_57 (6) = happyGoto action_13
action_57 (10) = happyGoto action_61
action_57 (11) = happyGoto action_15
action_57 (12) = happyGoto action_16
action_57 (13) = happyGoto action_17
action_57 (14) = happyGoto action_18
action_57 (15) = happyGoto action_19
action_57 (16) = happyGoto action_20
action_57 (20) = happyGoto action_21
action_57 (21) = happyGoto action_22
action_57 _ = happyFail

action_58 (22) = happyShift action_23
action_58 (29) = happyShift action_24
action_58 (30) = happyShift action_25
action_58 (31) = happyShift action_26
action_58 (32) = happyShift action_27
action_58 (33) = happyShift action_28
action_58 (34) = happyShift action_2
action_58 (35) = happyShift action_29
action_58 (36) = happyShift action_7
action_58 (4) = happyGoto action_11
action_58 (5) = happyGoto action_12
action_58 (6) = happyGoto action_13
action_58 (10) = happyGoto action_60
action_58 (11) = happyGoto action_15
action_58 (12) = happyGoto action_16
action_58 (13) = happyGoto action_17
action_58 (14) = happyGoto action_18
action_58 (15) = happyGoto action_19
action_58 (16) = happyGoto action_20
action_58 (20) = happyGoto action_21
action_58 (21) = happyGoto action_22
action_58 _ = happyFail

action_59 _ = happyReduce_35

action_60 _ = happyReduce_10

action_61 (23) = happyShift action_62
action_61 _ = happyFail

action_62 _ = happyReduce_36

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyTerminal (PT _ (TI happy_var_1)))
	 =  HappyAbsSyn4
		 ((read ( happy_var_1)) :: Integer
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  5 happyReduction_2
happyReduction_2 (HappyTerminal (PT _ (T_U happy_var_1)))
	 =  HappyAbsSyn5
		 (U (happy_var_1)
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  6 happyReduction_3
happyReduction_3 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn6
		 (PIdent (mkPosToken happy_var_1)
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happySpecReduce_1  7 happyReduction_4
happyReduction_4 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn7
		 (Defs happy_var_1
	)
happyReduction_4 _  = notHappyAtAll 

happyReduce_5 = happyReduce 4 8 happyReduction_5
happyReduction_5 ((HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	(HappyAbsSyn6  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Def happy_var_1 (reverse happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_6 = happySpecReduce_3  8 happyReduction_6
happyReduction_6 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn8
		 (DefType happy_var_1 happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_0  9 happyReduction_7
happyReduction_7  =  HappyAbsSyn9
		 ([]
	)

happyReduce_8 = happySpecReduce_1  9 happyReduction_8
happyReduction_8 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn9
		 ((:[]) happy_var_1
	)
happyReduction_8 _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  9 happyReduction_9
happyReduction_9 (HappyAbsSyn9  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn9
		 ((:) happy_var_1 happy_var_3
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 4 10 happyReduction_10
happyReduction_10 ((HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Lam happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_11 = happySpecReduce_1  10 happyReduction_11
happyReduction_11 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_11 _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_3  11 happyReduction_12
happyReduction_12 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Arr happy_var_1 happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_3  11 happyReduction_13
happyReduction_13 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn10
		 (Pi happy_var_1 happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  11 happyReduction_14
happyReduction_14 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_3  12 happyReduction_15
happyReduction_15 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Prod happy_var_1 happy_var_3
	)
happyReduction_15 _ _ _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  12 happyReduction_16
happyReduction_16 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn10
		 (Sigma happy_var_1 happy_var_3
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  12 happyReduction_17
happyReduction_17 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  13 happyReduction_18
happyReduction_18 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (Id happy_var_1 happy_var_3
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  13 happyReduction_19
happyReduction_19 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_2  14 happyReduction_20
happyReduction_20 (HappyAbsSyn10  happy_var_2)
	(HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (App happy_var_1 happy_var_2
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_1  14 happyReduction_21
happyReduction_21 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_21 _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_1  15 happyReduction_22
happyReduction_22 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn10
		 (Var happy_var_1
	)
happyReduction_22 _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_1  15 happyReduction_23
happyReduction_23 _
	 =  HappyAbsSyn10
		 (Nat
	)

happyReduce_24 = happySpecReduce_1  15 happyReduction_24
happyReduction_24 _
	 =  HappyAbsSyn10
		 (Suc
	)

happyReduce_25 = happySpecReduce_1  15 happyReduction_25
happyReduction_25 _
	 =  HappyAbsSyn10
		 (Rec
	)

happyReduce_26 = happySpecReduce_1  15 happyReduction_26
happyReduction_26 (HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn10
		 (NatConst happy_var_1
	)
happyReduction_26 _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_1  15 happyReduction_27
happyReduction_27 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn10
		 (Universe happy_var_1
	)
happyReduction_27 _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_3  15 happyReduction_28
happyReduction_28 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn10
		 (happy_var_2
	)
happyReduction_28 _ _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  16 happyReduction_29
happyReduction_29 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn16
		 (Arg happy_var_1
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_1  16 happyReduction_30
happyReduction_30 _
	 =  HappyAbsSyn16
		 (NoArg
	)

happyReduce_31 = happySpecReduce_0  17 happyReduction_31
happyReduction_31  =  HappyAbsSyn17
		 ([]
	)

happyReduce_32 = happySpecReduce_2  17 happyReduction_32
happyReduction_32 (HappyAbsSyn16  happy_var_2)
	(HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (flip (:) happy_var_1 happy_var_2
	)
happyReduction_32 _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_1  18 happyReduction_33
happyReduction_33 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn18
		 (Binder happy_var_1
	)
happyReduction_33 _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_1  19 happyReduction_34
happyReduction_34 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn19
		 ((:[]) happy_var_1
	)
happyReduction_34 _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_2  19 happyReduction_35
happyReduction_35 (HappyAbsSyn19  happy_var_2)
	(HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn19
		 ((:) happy_var_1 happy_var_2
	)
happyReduction_35 _ _  = notHappyAtAll 

happyReduce_36 = happyReduce 5 20 happyReduction_36
happyReduction_36 (_ `HappyStk`
	(HappyAbsSyn10  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (TypedVar happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_37 = happySpecReduce_1  21 happyReduction_37
happyReduction_37 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn21
		 ((:[]) happy_var_1
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_2  21 happyReduction_38
happyReduction_38 (HappyAbsSyn21  happy_var_2)
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn21
		 ((:) happy_var_1 happy_var_2
	)
happyReduction_38 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 38 38 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 22;
	PT _ (TS _ 2) -> cont 23;
	PT _ (TS _ 3) -> cont 24;
	PT _ (TS _ 4) -> cont 25;
	PT _ (TS _ 5) -> cont 26;
	PT _ (TS _ 6) -> cont 27;
	PT _ (TS _ 7) -> cont 28;
	PT _ (TS _ 8) -> cont 29;
	PT _ (TS _ 9) -> cont 30;
	PT _ (TS _ 10) -> cont 31;
	PT _ (TS _ 11) -> cont 32;
	PT _ (TS _ 12) -> cont 33;
	PT _ (TI happy_dollar_dollar) -> cont 34;
	PT _ (T_U happy_dollar_dollar) -> cont 35;
	PT _ (T_PIdent _) -> cont 36;
	_ -> cont 37;
	_ -> happyError' (tk:tks)
	}

happyError_ 38 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pDefs tks = happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn7 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--	trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 312 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
