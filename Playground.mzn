% Use this editor as a MiniZinc scratch book
int: n = 20; % Number of variables
array[1..n] of var 0..100: x; % Decision variables with a range

% Coefficients for the linear constraints
array[1..n] of int: coeffs = [3, 5, 2, 8, 6, 7, 1, 9, 4, 10, 2, 5, 3, 6, 7, 1, 8, 4, 9, 10];

% Constraint: Weighted sum of variables should be <= a given bound
constraint sum(i in 1..n) (coeffs[i] * x[i]) <= 150;

% Additional constraints (optional)
% constraint x[1] + x[2] <= 20;
% constraint x[3] + x[4] + x[5] <= 30;
% constraint x[6] + x[7] + x[8] <= 40;

% Objective function (optional, if optimization is needed)
% var int: obj = sum(i in 1..n) (x[i]);
solve satisfy
% solve maximize obj; % Change to 'satisfy' if no optimization is needed

% output ["Solution: \n" ++ concat(["x[" ++ show(i) ++ "] = " ++ show(x[i]) ++ "\n" | i in 1..n])];