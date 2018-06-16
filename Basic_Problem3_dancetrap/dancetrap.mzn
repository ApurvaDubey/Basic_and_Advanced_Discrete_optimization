% Beauty Trap
% Perform the most seductive dance

enum LEGS = {spin, leap, waltz, curtsey, prep, stand};
enum ARMS = {beckon, out, up, wrapped, neutral};
enum FACE = {smile, wink, batt, think, glow, blank};

int: maxlen;
set of int: STEP = 1..maxlen;
array[LEGS] of int: maxlegs;
array[ARMS] of int: maxarms;
array[FACE] of int: maxface;
constraint assert(maxlegs[stand] >= maxlen, "maxlegs[stand] smaller than maxlen");
constraint assert(maxarms[neutral] >= maxlen, "maxarms[neutral] smaller than maxlen");
constraint assert(maxface[blank] >= maxlen, "maxface[blank] smaller than maxlen");
array[LEGS,ARMS] of int: dance_value;
array[ARMS,FACE] of int: entice_value;
constraint assert(dance_value[stand,neutral] = 0, "incorrect dance_value array");
constraint assert(entice_value[neutral,blank] = 0, "incorrect entice_value array");
int: boredom; % how bored each step make the viewer

var STEP: len;
array[STEP] of var LEGS: legs;
array[STEP] of var ARMS: arms;
array[STEP] of var FACE: face;


/* 
LEGS constraints:
 > She must prep before any leap. 
 > Directly after a spin she can only curtsey, prep or stand.
 > Directly after a leap she can only spin, waltz, or stand. 
 > She can waltz at most three times in a row.
 > She cannot prep directly after a curtsey. 
 > Finally, in between any waltz and a following curtsey there must be a stand.
*/
constraint forall(i in 1..len-1)(legs[i+1] = leap -> legs[i] = prep);
constraint forall(i in 1..len-1)(legs[i] = spin -> (legs[i+1] in {curtsey, prep, stand}));
constraint forall(i in 1..len-1)(legs[i] = leap -> (legs[i+1] in {spin, waltz, stand}));
constraint forall(i in 1..len-3)((legs[i] = waltz /\ legs[i+1] = waltz /\ legs[i+2] = waltz) -> legs[i+3] != waltz);
constraint forall(i in 1..len-1)(legs[i] = curtsey -> legs[i+1] != prep);
constraint forall(i in 1..len-2)(legs[i] = waltz -> (
                                                          forall(j in i+2..len-1)((legs[j] = curtsey)
                                                                    -> exists(k in i+1..j-1)(legs[k] = stand))
                                                         )
                                 );


/*
ARMS constraints:
 > She can beckon only directly after out or up (and hence not as the first move).
 > She can wrapped only directly after beckon or neutral, including the possibility that wrapped is the
   first move (since the previous move can be considered neutral). 
 > She cannot do any of the two same moves in a row except neutral.
*/
constraint forall(i in 1..len-1)(arms[i+1] = beckon -> (arms[i] in {up,out}));
constraint (arms[1] != beckon);
constraint forall(i in 1..len-1)(arms[i+1] = wrapped -> arms[i] in {beckon,neutral});
constraint forall(i in 1..len-1)((arms[i] != neutral /\ arms[i+1] != neutral) -> arms[i] != arms[i+1]);

/*
FACE constraints:
 > She cannot make more than two of the same gestures in a row except blank. 
 > She cannot think directly after smile (ing) or batt (ing) her eyelids.
*/
constraint forall(i in 1..len-1)((face[i] != blank /\ face[i+1] != blank) -> face[i] != face[i+1]);
constraint forall(i in 1..len-1)((face[i] in {smile,batt}) -> face[i+1] != think);


/*
OTHERS constraints:
 > Some combinations of legs move and arms moves are impossible. 
 > Similarly some combinations of arms move and face would be very off putting and hence must be avoided.
 > After the dance ends she must stay in the base position stand, neutral, and blank.
*/
constraint forall(k in 1..len)(forall(i in LEGS, j in ARMS where dance_value[i,j] < 0)(legs[k] = i -> arms[k] != j));
constraint forall(k in 1..len)(forall(i in ARMS, j in FACE where entice_value[i,j] < 0)(arms[k] = i -> face[k] != j));
constraint forall(i in STEP)((i > len) -> (legs[i] = stand /\ arms[i] = neutral /\ face[i] = blank));

include "global_cardinality_low_up.mzn";
constraint global_cardinality_low_up(legs,LEGS,[0 | i in LEGS],[m | m in maxlegs]);
constraint global_cardinality_low_up(arms,ARMS,[0 | i in ARMS],[m | m in maxarms]);
constraint global_cardinality_low_up(face,FACE,[0 | i in FACE],[m | m in maxface]);

var int: obj = sum([dance_value[legs[i],arms[i]] | i in 1..len]) + sum([entice_value[arms[i],face[i]] | i in 1..len]) - boredom*(len);
solve maximize obj; 

output ["len = \(len);\n" , "legs = \(legs);\n", "arms = \(arms);\n", "face = \(face);\n","obj = \(obj);"];