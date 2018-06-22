int: T; % maximum time allowed;
set of int: TIME = 1..T;

int: E; % weight of elephant in STONES;
set of int: STONE = 0..E;

int: G; % number of guards
set of int: GUARD = 1..G;
array[GUARD] of STONE: easy;   
array[GUARD] of STONE: hard;
array[GUARD] of TIME: tired;

% breaking symmetry
constraint forall(g1 in GUARD,g2 in GUARD where g1 > g2)(
                    ((easy[g1] = easy[g2]) /\ (hard[g1] = hard[g2]) /\ (tired[g1] = tired[g2])) -> (sum(t in 1..T)(act[g1,t]) >= sum(t in 1..T)(act[g2,t])));
                                                                                
GUARD: p; % maximum people on pier;
GUARD: b; % maximum people on boat;

set of int: ACT = -1..E; % -1 = goto bank, 0 = wait, > 0 carry stones  
int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
var TIME: end;                            % end time;

%enum POS = {R,P,B}; % R:river, P:pier, B:Bank
array[GUARD,0..T] of var 0..1: pierCnt;      
array[GUARD,0..T] of var 0..1: boatCnt;      
array[GUARD,0..T] of var 0..1: bankCnt; 

% At the beginning all guards are at the Bank
constraint forall(g in GUARD)(bankCnt[g,0] = 1);
constraint forall(g in GUARD)(pierCnt[g,0] = 0);
constraint forall(g in GUARD)(boatCnt[g,0] = 0);

% After the end time each guard must only wait.
constraint forall(g in GUARD, t in 1..T)((t > end) -> (act[g,t] = 0));
% ...and just stay put where they were at the end
constraint forall(g in GUARD, t in 1..T)((t > end) -> (bankCnt[g,t] = bankCnt[g,end]));
constraint forall(g in GUARD, t in 1..T)((t > end) -> (boatCnt[g,t] = boatCnt[g,end]));
% ...and not one is walking on the pier
constraint forall(g in GUARD, t in 1..T)((t > end) -> (pierCnt[g,t] = 0));

% p is the maximum number of guards on the pier one time, 
constraint forall(t in 1..end)(sum(g in GUARD where pierCnt[g,t] = 1)(1) <= p);

% and b is the maximum number of guards on the boat at one time.
constraint forall(t in 1..end)(sum(g in GUARD where boatCnt[g,t] = 1)(1) <= b);

% channeling constraint between 'pos' and 'act'
 % if the gurad was walking toward bank or taking stones from bank to boat then pierCnt = 1 (bi-directional)
   constraint forall(t in 1..end, g in GUARD)((act[g,t] = -1 \/ act[g,t] > 0) <-> pierCnt[g,t] = 1);
 % if the gurad was resting then pierCnt = 1 (bi-directional)
   constraint forall(t in 1..end, g in GUARD)((act[g,t] = 0) <-> pierCnt[g,t] = 0);

 % if the gurad was taking stones from bank to boat then then boatCnt = 1
   constraint forall(t in 1..end, g in GUARD)((act[g,t] > 0) -> boatCnt[g,t] = 1);
 % if the gurad was walking back to bank then then boatCnt = 0
   constraint forall(t in 1..end, g in GUARD)((act[g,t] = -1) -> boatCnt[g,t] = 0);
   
 % if the gurad was walking back to bank then then he must have been on the boat at 't-1'
   constraint forall(t in 1..end, g in GUARD)((act[g,t] = -1) -> boatCnt[g,t-1] = 1);
   
 % if the gurad had taken stones to boat in the previous timestep and is resting in curent time step then he's at boat
   constraint forall(t in 1..end, g in GUARD)((act[g,t-1] > 0 /\ act[g,t] = 0) -> boatCnt[g,t] = 1);
 % if the guard was resting previous timestep and is resting in curent time step an was at the boat in previous timestep then he's at boat in the current timestep too
   constraint forall(t in 1..end, g in GUARD)((act[g,t-1] = 0 /\ act[g,t] = 0 /\ boatCnt[g,t-1] = 1) -> boatCnt[g,t] = 1);

 % if the gurad is walking toward bank then he will be at the bank
   constraint forall(t in 1..end, g in GUARD)((act[g,t] = -1) -> (boatCnt[g,t-1] = 1 /\ bankCnt[g,t] = 1));
 % if the gurad is walking toward bank in the previous timestep and is resting now then he will be at the bank
   constraint forall(t in 1..end, g in GUARD)((act[g,t-1] = -1 /\ act[g,t] = 0) -> bankCnt[g,t] = 1);
 % if the guard had carried stones in the current timestep then he must be at the bank in the previous timestep
   constraint forall(t in 1..end, g in GUARD)((act[g,t] > 0) -> bankCnt[g,t-1] = 1);
 % if the guard was resting in the previous and current timestep and was at the bank in previous timestep then he must be at the bank even in current timestep 
   constraint forall(t in 1..end, g in GUARD)((act[g,t-1] = 0 /\ act[g,t] = 0 /\ bankCnt[g,t-1] = 1) -> bankCnt[g,t] = 1);


 % if the guard was at the boat in previous timestep and at the bank in current timestep then he should have walked from boat to bank
   constraint forall(t in 1..end, g in GUARD)((boatCnt[g,t-1] = 1 /\ bankCnt[g,t] = 1) <-> act[g,t] = -1);
 % if the guard was at the boat in previous timestep and at the bank in current timestep then he should have walked the pier too
   constraint forall(t in 1..end, g in GUARD)((boatCnt[g,t-1] = 1 /\ bankCnt[g,t] = 1) -> pierCnt[g,t] = 1);
 % if the guard was at the bank in previous timestep and at the boat in current timestep then he should have walked the pier too
   constraint forall(t in 1..end, g in GUARD)((bankCnt[g,t-1] = 1 /\ boatCnt[g,t] = 1) -> pierCnt[g,t] = 1);


% if in step 't' the gurad took stones from bank to boat
% then at step 't+1' he cannot be carrying stones 
constraint forall(g in GUARD, t in 1..(end-1))(act[g,t] > 0 -> act[g,t+1] <= 0);

% a total of E stones have to be taken to the boat
constraint sum(g in GUARD, t in 1..end where act[g,t] > 0)(act[g,t]) >= E;

% upper limit on the number of stones that can be taken by each guard {hard}
constraint forall(g in GUARD, t in 1..end where act[g,t] > 0)(act[g,t] in {easy[g], hard[g]});

% if the number of stones that a guard has carried are more than easy[g]
% then (s)he wil have to wait out a few steps
constraint forall(g in GUARD, t in 1..end)
                    ((act[g,t] > easy[g]) -> (forall(t2 in (t+1)..(t+tired[g]))(act[g,t2] <= 0)));

% in any time step all of them have to move in the same direction: either from bank to boat or
% boat to bank.
constraint forall(t in 1..end, g1 in GUARD, g2 in GUARD where (g1 > g2) /\ (act[g1,t] != 0) /\ (act[g2,t] != 0))
                          (act[g1,t] > 0 -> act[g2,t] > 0);

constraint forall(t in 1..end, g1 in GUARD, g2 in GUARD where (g1 > g2) /\ (act[g1,t] != 0) /\ (act[g2,t] != 0))
                          (act[g1,t] < 0 -> act[g2,t] < 0);

solve 
:: 
seq_search([
int_search(array1d(act), first_fail, indomain_random, complete)
%int_search(array1d(boatCnt), first_fail, indomain_random, complete),
%int_search(array1d(pierCnt), first_fail, indomain_random, complete)
])
minimize end;

output ["\nact = array2d(GUARD,TIME,\(act));\nend = \(end);"];