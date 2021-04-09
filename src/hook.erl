%%%-------------------------------------------------------------------
%%% @doc
%%% hook module:function/arity replace with callback_module:callback_function/arity
%%% @end
%%%-------------------------------------------------------------------
-module(hook).
-export([hook/4, hook/5]).
-export([unload/1]).
%% asm header
-include_lib("compiler/src/beam_disasm.hrl").
-include_lib("compiler/src/beam_opcodes.hrl").
%% code decode state and term
-record(state, {tag = 0, term, offset = 0, first = 0, bytes = <<>>, atoms, literals}).
-record(term, {name, data = 0, offset = 0}).
%% tag define
-define(TAG_LITERAL,                                  0).
-define(TAG_INTEGER,                                  1).
-define(TAG_ATOM,                                     2).
-define(TAG_X_REGISTER,                               3).
-define(TAG_Y_REGISTER,                               4).
-define(TAG_LABEL,                                    5).
-define(TAG_CHARACTER,                                6).
-define(TAG_EXT_FLOAT,                                7).
-define(TAG_EXT_LIST,                                 8).
-define(TAG_EXT_FLOAT_REGISTER,                       9).
-define(TAG_EXT_ALLOC_LIST,                           10).
-define(TAG_EXT_LITERAL,                              11).
-define(TAG_UNKNOWN,                                  12).
%%%===================================================================
%%% API
%%%===================================================================
%% @dod hook module:function replace with callback_module:callback_function
-spec hook(Module :: module(), Function :: atom(), Arity :: arity(), CallbackModule :: module()) -> {module, module()} | {error, term()}.
hook(Module, Function, Arity, CallbackModule) ->
    hook(Module, Function, Arity, CallbackModule, Function).

%% @dod hook module:function replace with callback_module:callback_function
-spec hook(Module :: module(), Function :: atom(), Arity :: arity(), CallbackModule :: module(), CallbackFunction :: atom()) -> {module, module()} | {error, term()}.
hook(Module, Function, Arity, CallbackModule, CallbackFunction) ->
    File = code:which(Module),
    {_, _, Chunks} = beam_lib:all_chunks(File),
    {_, {_, [{atoms, Atoms}, {indexed_imports, Imports}, {"CInf", CompileInfoChunk}, {"Code", Code}]}} = beam_lib:chunks(File, [atoms, indexed_imports, "CInf", "Code"]),
    %% remove native
    CompileInfo = binary_to_term(CompileInfoChunk),
    Options = proplists:get_value(options, CompileInfo, []),
    NewCompileInfo = term_to_binary(lists:keyreplace(options, 1, CompileInfo, {options, lists:delete(native, Options)})),
    %% rebuild atom and import dict
    AtomsDict = setelement(2, beam_dict:new(), lists:foldl(fun({I, A}, M) -> maps:put(A, I, M) end, maps:new(), Atoms)),
    ImportsDict = lists:foldl(fun({_, M, F, A}, D) -> element(2, beam_dict:import(M, F, A, D)) end, AtomsDict, Imports),
    {ImportIndex, Dict} = beam_dict:import(CallbackModule, CallbackFunction, Arity, ImportsDict),
    %% rebuild atom table
    {NumberAtoms, AtomTable} = beam_dict:atom_table(Dict, utf8),
    AtomChunk = <<NumberAtoms:32, (iolist_to_binary(AtomTable))/binary>>,
    %% rebuild import table
    {NumberExports, ImportTable} = beam_dict:import_table(Dict),
    ImportChunk = <<NumberExports:32, (<<<<F:32, A:32, L:32>> || {F, A, L} <- ImportTable>>)/binary>>,
    %% rebuild code
    <<SubSize:32, _:32, OpCodeMax:32, NumberLabels:32, NumberFunctions:32, Bytes/binary>> = Code,
    List = decode_code(#state{bytes = Bytes, atoms = gb_trees:from_orddict(Atoms)}, []),
    Offset = match_label(List, Module, Function, Arity),
    Offset =:= 0 andalso exit({function_label_not_found, Module, Function, Arity}),
    <<Head:Offset/binary-unit:8, Tail/binary>> = Bytes,
    %% build code
    CallLabel = <<(beam_opcodes:opcode(call_ext_only, 2)):8, (list_to_binary([beam_asm:encode(?tag_u, Arity)]))/binary, (list_to_binary([beam_asm:encode(?tag_u, ImportIndex)]))/binary>>,
    Label = <<(beam_opcodes:opcode(label, 1)):8, (list_to_binary([beam_asm:encode(?tag_u, NumberLabels)]))/binary>>,
    CodeHeader = <<SubSize:32, (beam_opcodes:format_number()):32, (max(OpCodeMax, beam_opcodes:opcode(call_ext_only, 2))):32, (NumberLabels + 1):32, NumberFunctions:32>>,
    CodeChunk = <<CodeHeader/binary, Head/binary, CallLabel/binary, Label/binary, Tail/binary>>,
    %% replace chunks
    ReplaceCompileInfoChunks = lists:keyreplace("CInf", 1, Chunks, {"CInf", NewCompileInfo}),
    ReplaceAtomChunks = lists:keyreplace("AtU8", 1, ReplaceCompileInfoChunks, {"AtU8", AtomChunk}),
    ReplaceImportChunks = lists:keyreplace("ImpT", 1, ReplaceAtomChunks, {"ImpT", ImportChunk}),
    ReplaceCodeChunks = lists:keyreplace("Code", 1, ReplaceImportChunks, {"Code", CodeChunk}),
    %% remove native(hipe) chunk if exists
    ChunkName = case lists:member(native, Options) of true -> hipe_unified_loader:chunk_name(erlang:system_info(hipe_architecture)); false -> "" end,
    FinalChunks = lists:keydelete(ChunkName, 1, ReplaceCodeChunks),
    %% rebuild module
    {ok, Binary} = beam_lib:build_module(FinalChunks),
    code:unstick_mod(Module),
    code:load_binary(Module, File, Binary).

%% @doc unload hook module
-spec unload(Module :: module()) -> boolean().
unload(Module) ->
    code:unstick_mod(Module),
    File = code:which(Module),
    {ok, Binary} = file:read_file(File),
    code:load_binary(Module, File, Binary).

%%%===================================================================
%%% Internal functions
%%%===================================================================
%% find function label
match_label([], _, _, _) ->
    0;
match_label([#term{name = func_info, data = [#term{name = atom, data = Module}, #term{name = atom, data = Function}, #term{name = integer, data = Arity}]}, #term{name = label}, #term{offset = Offset} | _], Module, Function, Arity) ->
    %% label next term start offset
    Offset - 1;
match_label([_ | T], Module, Function, Arity) ->
    match_label(T, Module, Function, Arity).

%% decode code instruction
decode_code(#state{offset = Offset, bytes = Bytes}, List) when Offset == byte_size(Bytes) ->
    lists:reverse(List);
decode_code(State = #state{offset = Offset, bytes = Bytes}, List) ->
    <<_:Offset/binary-unit:8, First:8, _/binary>> = Bytes,
    NewState = #state{term = Term} = decode_instr(State#state{offset = Offset + 1, first = First}),
    decode_code(NewState, [Term | List]).

decode_instr(State = #state{offset = Offset, first = First}) ->
    {SymOp, Arity} = bo:opname(First),
    case SymOp of
        select_val ->
            decode_select(select_val, State);
        select_tuple_arity ->
            decode_select(select_tuple_arity, State);
        put_map_assoc ->
            decode_map(put_map_assoc, Arity, State);
        put_map_exact ->
            decode_map(put_map_exact, Arity, State);
        get_map_elements ->
            decode_map(get_map_elements, Arity, State);
        has_map_fields ->
            decode_map(has_map_fields, Arity, State);
        _ ->
            {NewState, List} = decode_number_term(Arity, State, []),
            NewState#state{term = #term{name = SymOp, data = List, offset = Offset}}
    end.

decode_select(Name, State = #state{offset = Offset}) ->
    {NewState, [X, F, Z, U = #term{data = Length}]} = decode_number_term(4, State, []),
    {NewestState, List} = decode_number_term(Length, NewState, []),
    Term = #term{name = Name, data = [X, F, {Z, U, List}], offset = Offset},
    NewestState#state{term = Term}.

decode_map(Name, Arity, State = #state{offset = Offset}) ->
    {NewState, FirstList} = decode_number_term(Arity, State, []),
    [Z | T] = lists:reverse(FirstList),
    A = lists:reverse(T),
    NewestState = #state{term = U = #term{data = Length}} = decode_tag_term(NewState),
    {FinalState, SecondList} = decode_number_term(Length, NewestState, []),
    Term = #term{name = Name, data = A ++ [{Z, U, SecondList}], offset = Offset},
    FinalState#state{term = Term}.

%% decode number of term
decode_number_term(0, State, List) ->
    {State, lists:reverse(List)};
decode_number_term(Number, State, List) ->
    NewState = #state{term = Term} = decode_tag_term(State),
    decode_number_term(Number - 1, NewState, [Term | List]).

%% decode term with tag
decode_tag_term(State = #state{offset = Offset, bytes = Bytes}) ->
    <<_:Offset/binary-unit:8, First:8, _/binary>> = Bytes,
    Flag = case erlang:list_to_integer(erlang:system_info(otp_release)) >= 20 of true -> 1; false -> 0 end,
    Index = First band 2#111,
    Tag = case Index >= 7 of true -> 6 + (First bsr 4) + Flag; false -> Index end,
    Tag >= ?TAG_UNKNOWN andalso exit({unknown, tag, Tag, State}),
    decode_term(State#state{tag = Tag, offset = Offset + 1, first = First}).

%% decode term
decode_term(State = #state{tag = ?TAG_ATOM, offset = Offset, atoms = Atoms}) ->
    %% do not decode tag
    NewState = #state{term = Term = #term{data = Index}} = decode_term(State#state{tag = ?TAG_INTEGER}),
    {Name, Data} = if Index =:= 0 -> {nil, []}; true -> {atom, gb_trees:get(Index, Atoms)} end,
    NewState#state{term = Term#term{name = Name, data = Data, offset = Offset}};

decode_term(State = #state{tag = ?TAG_EXT_FLOAT, offset = Offset, bytes = Bytes}) ->
    <<_:Offset/binary-unit:8, Float:64/float, _/binary>> = Bytes,
    Term = #term{name = float, data = Float, offset = Offset},
    State#state{term = Term, offset = Offset + 8};

decode_term(State = #state{tag = ?TAG_EXT_LIST, offset = Offset, first = First}) ->
    Term = #term{name = list, data = First bsr 4, offset = Offset},
    State#state{term = Term};

decode_term(State = #state{tag = ?TAG_EXT_FLOAT_REGISTER, offset = Offset}) ->
    NewState = #state{term = Term} = decode_tag_term(State),
    NewState#state{term = Term#term{name = float_register, offset = Offset}};

decode_term(State = #state{tag = ?TAG_EXT_ALLOC_LIST, offset = Offset}) ->
    NewState = #state{term = #term{data = Number}} = decode_tag_term(State),
    NewestState = #state{term = Term} = decode_term_loop(Number, NewState, []),
    NewestState#state{term = Term#term{name = alloc_list, offset = Offset}};

decode_term(State = #state{tag = ?TAG_EXT_LITERAL, offset = Offset}) ->
    NewState = #state{tag = Tag, term = Term} = decode_tag_term(State),
    Tag =/= ?TAG_LITERAL andalso exit({decode_literal, NewState}),
    %% @todo literal table convert
    %% @beam_disam.erl:534
    NewState#state{term = Term#term{name = literal, offset = Offset}};

decode_term(State = #state{offset = Offset, first = First}) when (First band 16#08) =:= 0 ->
    Term = #term{name = integer, data = First bsr 4, offset = Offset},
    State#state{term = Term};

decode_term(State = #state{first = First, offset = Offset, bytes = Bytes}) when (First band 16#10) =:= 0 ->
    <<_:Offset/binary-unit:8, Second:8, _/binary>> = Bytes,
    Term = #term{name = integer, data = (((First band 2#11100000) bsl 3) bor Second), offset = Offset},
    State#state{term = Term, offset = Offset + 1};

decode_term(State = #state{tag = Tag, offset = Offset, bytes = Bytes}) ->
    NewState = #state{term = #term{data = Length}, offset = NewOffset} = decode_integer(State),
    <<_:NewOffset/binary-unit:8, IntegerBytes:Length/binary-unit:8, _/binary>> = Bytes,
    %% (Bn << 8 * n) bor ... bor (B1 << 8) bor (B0 << 0)
    Integer = lists:foldl(fun(B, N) -> (N bsl 8) bor B end, 0, binary_to_list(IntegerBytes)),
    %% negative
    Data = case binary:first(IntegerBytes) > 127 andalso Tag == ?TAG_INTEGER of true -> Integer - (1 bsl (Length * 8)); false -> Integer end,
    Term = #term{name = integer, data = Data, offset = Offset},
    NewState#state{term = Term, offset = NewOffset + Length}.

decode_term_loop(0, State, List) ->
    Term = #term{data = lists:reverse(List)},
    State#state{term = Term};
decode_term_loop(Number, State, List) ->
    NewState = #state{term = Type} = decode_tag_term(State),
    NewestState = #state{term = Value} = decode_tag_term(NewState),
    %% @todo literal table convert
    %% @beam_disam.erl:568
    decode_term_loop(Number - 1, NewestState, [{Type, Value} | List]).

decode_integer(State = #state{offset = Offset, first = First}) when First bsr 5 == 7 ->
    NewState = #state{tag = Tag, term = Term = #term{data = Data}} = decode_tag_term(State),
    Tag =/= ?TAG_LITERAL andalso exit({decode_integer, weird_bignum_sub_length, NewState}),
    NewState#state{term = Term#term{data = Data + 9, offset = Offset}};
decode_integer(State = #state{offset = Offset, first = First}) ->
    State#state{term = #term{name = integer, data = (First bsr 5) + 2, offset = Offset}}.
