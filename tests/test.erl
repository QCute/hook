-module(test).
-export([test/0]).
-export([concat/1]).

test() ->
    hook:hook(lists, concat, 1, ?MODULE).

concat(Thing) ->
    io:format("hey! is me: ~p~n", [Thing]).
