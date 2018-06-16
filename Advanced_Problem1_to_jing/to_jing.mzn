% Liu Bei forsees that Yuan Shiu will be defeated by Cao Cao
% He needs to find a route to safety in Jin province before the defeat
% But Cao Cao's soldiers are everywhere

int: nrow;
set of int: ROW = 1..nrow;
int: ncol;
set of int: COL = 1..ncol;

% Plains, Mountain, Forest, City, River
enum TERRAIN = { P, M, F, C, R };
array[TERRAIN] of int: delay;
int: timelimit;

array[ROW,COL] of TERRAIN: terrain;
array[ROW,COL] of int: soldier;
array[ROW,COL] of bool: Jin;

int: start_row;
int: start_col;

int: maxstep;
set of int: STEP = 1..maxstep;
set of int: STEP0 = 0..maxstep;

var STEP: steps;
array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited
array[STEP] of var 0..nrow*ncol: idxstep;
constraint forall(i in STEP)((i > steps) -> idxstep[i] = 0);


% start at start position
constraint visit[start_row,start_col] = 1;
constraint idxstep[1] = (start_row-1)*(ncol) + start_col;

% only use steps moves
constraint sum(r in ROW, c in COL)(visit[r,c] >= 1) <= steps;

% reach Jin province
%constraint exists(r in ROW, c in COL)(Jin[r,c] /\ visit[r,c] >= 1);
constraint sum(r in ROW, c in COL where Jin[r,c] /\ visit[r,c] >= 1)(1) = 1;

% reach Jin province: complimentary costraint
constraint sum(s in idxstep where s != 0 /\
                        Jin[((s div nrow) + min(s mod ncol,1)),(if (s mod ncol) = 0 then ncol else (s mod ncol) endif)])(1) = 1;

% channel constraint
%constraint forall(r in ROW, c in COL where visit[r,c] > 1)(idxstep[visit[r,c]] =  (r-1)*ncol + c);
constraint forall(r in ROW, c in COL)(visit[r,c] > 1 -> (idxstep[visit[r,c]]  =  (r-1)*ncol + c));
constraint forall(s in idxstep where s != 0) 
                        (visit[((s div nrow) + min(s mod ncol,1)),(if (s mod ncol) = 0 then ncol else (s mod ncol) endif)] >= 1);

constraint forall(r in ROW, c in COL where visit[r,c] >= 1)(
                    (r = ((idxstep[visit[r,c]] div nrow) + min(idxstep[visit[r,c]] mod ncol,1))) /\
                    (c = (if (idxstep[visit[r,c]] mod ncol) = 0 then ncol else (idxstep[visit[r,c]] mod ncol) endif))
                    );


% visit at most one city
constraint sum(r in ROW, c in COL where terrain[r,c] = C /\ visit[r,c] >= 1)(1) <= 1;

% complementary constraint
constraint sum(s in idxstep where s != 0 /\ 
               terrain[((s div nrow) + min(s mod ncol,1)),(if (s mod ncol) = 0 then ncol else (s mod ncol) endif)] = C)(1) <= 1;



% cant enter Mountain
%constraint not exists(r in ROW, c in COL)(terrain[r,c] = M /\ visit[r,c] >= 1);
constraint sum(r in ROW, c in COL where terrain[r,c] = M /\ visit[r,c] >= 1)(1) = 0;

% cant enter Mountain: complementary constraint
constraint forall(s in idxstep where s != 0) 
                (terrain[((s div nrow) + min(s mod ncol,1)),(if (s mod ncol) = 0 then ncol else (s mod ncol) endif)] != M);

% visit only one place in every step
%constraint sum(r in ROW, c in COL where visit[r,c] >= 1)(1) = steps;

include "alldifferent_except_0.mzn";
constraint alldifferent_except_0([visit[r,c] | r in ROW, c in COL]);
constraint alldifferent_except_0(idxstep);

% steps form a path
constraint forall(s in 1..steps-1)
                 (exists(r1, r2 in ROW, c1, c2 in COL where (r1*ncol+c1) != (r2*ncol+c2))
                        (abs(r1-r2) + abs(c1-c2) = 1 
                         /\ visit[r1,c1] = s+1 /\ visit[r2,c2] = s));

% steps form a path: complimentary constraint
constraint forall(s in 1..steps-1)
 (abs(((idxstep[s+1] div nrow) + min(idxstep[s+1] mod ncol,1)) - ((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1))) + 
  abs((if (idxstep[s+1] mod ncol) = 0 then ncol else (idxstep[s+1] mod ncol) endif) - (if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif)) 
  = 1);

                
% no shortcuts
constraint forall(r1,r2 in ROW, c1,c2 in COL where ((r1*ncol+c1) != (r2*ncol+c2)))
                 (abs(r1-r2) + abs(c1-c2) = 1 ->
                  visit[r1,c1] = 0 \/ visit[r2,c2] = 0 \/
                  abs(visit[r1,c1] - visit[r2,c2]) = 1);

% no shortcuts: complimentatry constraint
constraint forall(s in 1..steps-1)
 (
   ( ((idxstep[s+1] div nrow) + min(idxstep[s+1] mod ncol,1)) = ((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1)) )
   \/
   ( (if (idxstep[s+1] mod ncol) = 0 then ncol else (idxstep[s+1] mod ncol) endif)  = (if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif) )
 );

% not too much delay
var int: time = sum(r in ROW, c in COL)(delay[terrain[r,c]]*(visit[r,c] >= 1));

constraint time = sum(s in 1..steps)(
          delay[terrain[((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1)),(if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif)]]*(visit[((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1)),(if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif)] >= 1));
          
constraint time <= timelimit;

% minimize the number of soldiers traversed
%var int: obj = sum(r in ROW, c in COL)((visit[r,c] > 0)*soldier[r,c]);
var int: obj = sum(r in ROW, c in COL)((visit[r,c] >= 1)*soldier[r,c]);

constraint obj = sum(s in 1..steps)(
          soldier[((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1)),(if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif)]*(visit[((idxstep[s] div nrow) + min(idxstep[s] mod ncol,1)),(if (idxstep[s] mod ncol) = 0 then ncol else (idxstep[s] mod ncol) endif)] >= 1));


solve 
:: 
seq_search([
int_search(idxstep, first_fail, indomain_random, complete)
% int_search(visit, first_fail, indomain_random, complete)
% int_search(westend, first_fail, indomain_random, complete)
% int_search(stack, first_fail, indomain_random, complete)
])
minimize obj;


%array[STEP] of var int: rx = [(s div nrow) + min(s mod ncol,1) | s in idxstep];
%array[STEP] of var int: cx = [(if (s mod ncol) = 0 then ncol else (s mod ncol) endif) | s in idxstep];                        

array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];

output %[show(rx) ++ "\n"] ++ [show(cx) ++ "\n"] ++ [show(idxstep) ++ "\n"] ++
       %[show((if (1 mod ncol) = 0 then ncol else (1 mod ncol) endif)) ++ "\n"] ++ 
       %[show(idxstep) ++ "\n"] ++ 
       %[show(rx) ++ "\n"] ++ 
       %[show(cx) ++ "\n"] ++ 
       ["%"] ++
       [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\n%"] ++
       [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
         ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\n"] ++
       ["%"] ++
       [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
         ++ if c = ncol then "\n%" else "" endif
       | r in ROW, c in COL ]
       ++ ["\nvisit = array2d(ROW,COL,\(visit));\nsteps = \(steps);\ntime = \(time);\nobj = \(obj);"]
       ;


