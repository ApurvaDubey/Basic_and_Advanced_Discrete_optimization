% assignment 2
% select a set of raiding warrior
enum WARRIOR;
WARRIOR: dummy; 
enum CLAN; % the clan they belong too

int: l; % minimum raid party size
int: u; % maximum raid party size
int: m; % limit of hatreds

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;

array[CLAN,CLAN] of 0..1: hates;

array[1..u] of var WARRIOR: choose;

constraint sum([1 | w in choose where w != dummy]) <= u;
constraint sum([1 | w in choose where w != dummy]) >= l;

constraint forall(i in 1..u-1)
    (choose[i] >= (choose[i]!=dummy)+choose[i+1]);

var int: hatreds = sum([ hates[clan[w_i],clan[w_j]] | w_i, w_j in choose where w_i < w_j]);
constraint hatreds <= m;

var int: obj = sum([strength[w] | w in choose]);
solve maximize obj;

output ["raid = {"] ++ [if fix(choose[i]) != dummy then show(choose[i]) ++ if i < u /\ fix(choose[i+1]) != dummy then ", " else "" endif else "" endif | i in 1..u ] ++ ["};"] ++ ["\nobj = ",(show(obj))] ++ [";"];
