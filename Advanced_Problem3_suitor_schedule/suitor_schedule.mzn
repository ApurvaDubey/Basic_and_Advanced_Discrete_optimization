% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
set of int: MEETINGX = 1..n+1;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue }; % type of rooms

array[SUITOR,ROOM] of int: mintime; % minimum time the given suitor will spend in given room
array[SUITOR,ROOM] of int: maxtime; % maximum time the given suitor will spend in given room
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r]  >= 1 /\ maxtime[s,r] >= mintime[s,r], 
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move; % time to move between rooms
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays;

array[MEETINGX] of var TIME: start;
array[MEETINGX] of var TIME: dur;    % duration in false schedule
array[MEETINGX] of var TIME: end = [ (start[m] + dur[m]) | m in MEETINGX]; 
array[MEETINGX] of var ROOM: room;
array[MEETING] of var MEETINGX: next_meeting;

constraint start[n+1] = 24*ndays;
constraint dur[n+1] = 0;

include "alldifferent.mzn";

constraint alldifferent(next_meeting);
constraint alldifferent([start[next_meeting[m]] | m in MEETING]);
constraint forall(m in MEETING)((start[next_meeting[m]] >= end[m] + move[room[m],room[next_meeting[m]]]));

%set of int: KUNGFU = 1..n;
array[MEETING] of var 1..ndays*48: kungfu;  % start time for each lesson
array[MEETING] of var 0..1: kungfu_happens;  % bool flag if the meeting is gonna happen or not


% no overlap with other meetings
constraint forall(m in MEETING where room[m] = Red)(
            (end[m] mod 24 <= usedstart[Red]) \/
            (start[m] mod 24 >= usedstart[Red] + useddur[Red])
            );

constraint forall(m in MEETING where room[m] = Blue)(
            (end[m] mod 24 <= usedstart[Blue]) \/
            (start[m] mod 24 >= usedstart[Blue] + useddur[Blue])
            );
            
constraint forall(m in MEETING where room[m] = Gold)(
            (end[m] mod 24 <= usedstart[Gold]) \/
            (start[m] mod 24 >= usedstart[Gold] + useddur[Gold])
            );

% non overlap of meetings in a room
constraint forall (m1 in MEETING, m2 in MEETING where m1 > m2)
          (end[m1] <= start[m2] \/ start[m1] >= end[m2] );
          
constraint forall (m1 in MEETING, m2 in MEETING where m1 > m2 /\ room[m1] = Red /\ room[m2] = Red)
          (end[m1] <= start[m2] \/ start[m1] >= end[m2] );

constraint forall (m1 in MEETING, m2 in MEETING where m1 > m2 /\ room[m1] = Blue /\ room[m2] = Blue)
          (end[m1] <= start[m2] \/ start[m1] >= end[m2] );

constraint forall (m1 in MEETING, m2 in MEETING where m1 > m2 /\ room[m1] = Gold /\ room[m2] = Gold)
          (end[m1] <= start[m2] \/ start[m1] >= end[m2] );
%constraint disjunctive([start[m] | m in MEETING where room[m] = Red],[dur[m] | m in MEETING where room[m] = Red]);

% meetings should be between start and end time
constraint forall(m in MEETING)((start[m] mod 24) >= earliest /\ (start[m] mod 24) <= latest);
constraint forall(m in MEETING)((end[m] mod 24) <= latest /\ (end[m] mod 24) >= earliest  );

% all different start and end times
include "alldifferent.mzn";
constraint alldifferent(start);
constraint alldifferent(end);

% model for duration
  % kungfu lessions will affect minimum meeting time
constraint stage = C ->  (forall(m in MEETING)
          (if kungfu_happens[m] = 1 
           then dur[m] >= (mintime[suitor[m],room[m]] + lessontime) 
           else dur[m] >= mintime[suitor[m],room[m]]
           endif));

constraint stage != C -> forall(m in MEETING)(dur[m] >= mintime[suitor[m],room[m]]);

constraint forall(m in MEETING)(dur[m] <= maxtime[suitor[m],room[m]]);

% model for minseparation for kungfu lessons
constraint stage = C -> (forall (m1 in MEETING, m2 in MEETING where m1 > m2)
                       ((kungfu_happens[m1] = 1 /\ kungfu_happens[m2] = 1) -> 
                       (if start[m1] < start[m2]
                       then ((end[m2] - lessontime)-end[m1]) >= minsep
                       else ((end[m1] - lessontime)-end[m2]) >= minsep
                       endif)
                       ));

% meetings where kungfu is not gonna happen
constraint stage = C -> (forall (m1 in MEETING, m2 in MEETING where m1 > m2)
                       ((kungfu_happens[m1] = 0 /\ kungfu_happens[m2] = 0) -> 
                       (if start[m1] < start[m2]
                       then (kungfu[m2]-kungfu[m1]) >= minsep
                       else (kungfu[m1]-kungfu[m2]) >= minsep
                       endif)
                       ));
                     
% set kungfu to ndays*24+1
constraint stage = C -> 
          (forall(m in MEETING)
          (if kungfu_happens[m] = 1 
          then kungfu[m] = end[m] - lessontime
          else kungfu[m] > ndays*24
          endif));

% all kungfu lessons start at a different time and if not stage C then all lessons start at the same time after end of time
constraint if stage = C then alldifferent(kungfu)
              else forall(m in MEETING)(kungfu[m] = ndays*24 + 1)
                 endif;
         
%disjunctive(<start time array>, <duration array>)
%ensure no two tasks in the array overlap in execution

% objective functions
var int: obj = sum(m in MEETING where suitor[m] = LiuBei)(dur[m]) + 
                  if stage = C then sum(m in MEETING where kungfu_happens[m] = 1)(100) else 0 endif ;
solve maximize obj; % makespan;
 
include "arg_sort.mzn";
output ["\nstart = \([start[m] | m in MEETING]);\ndur = \([dur[m] | m in MEETING]);\nroom = \([room[m] | m in MEETING]);\nkungfu = \([kungfu[a] | a in arg_sort(kungfu)]);\nobj = \(obj);"];

