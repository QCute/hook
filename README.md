# Hook
* hook module:function/arity replace with callback_module:callback_function/arity

# quick start
* Add to rebar.config
```erlang
{deps, [
  ...
  {hook, {git, "https://github.com/QCute/hook.git", {branch, "master"}}}
]}.
```

* Usage 
```erlang
%% hook it
hook(lists, concat, 1, ?MODULE).
%% callback 
concat(Thing) -> io:format("hey! is me: ~p~n", [Thing]).
```
