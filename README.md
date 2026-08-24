# Reverse-and-Add / F*

Phase 1/2 のモデルと、汎用の有限抽象 checker です。桁は little-endian（最下位桁から）で、空リストを 0 とします。

`ReverseAdd.fst` は次を検証します。

- 基数・桁・数表現、正規化、値関数
- 正規化付き桁反転
- 自然数からの桁列復元と `reverse_base`
- carry を含む桁単位加算
- `reverse_add`、回文 predicate、`step` 関係
- `value (reverse_digits xs) == reverse_base (value xs)`（canonical 入力）
- `value (reverse_add xs) == value xs + reverse_base (value xs)`（canonical 入力）
- `predecessor`、`iterate`、`reaches`
- `56 -> 121`、`196 -> 887`、base 2 の検算

`ReverseAddCarry.fst` は桁加算の output と carry profile を同時に追跡し、
既存の `add_digits` と output が一致することを検証します。196 の一段目の carry profile
も固定値として確認し、同じ出力桁を生む対称セルでは carry in/out が一致する必要条件を置いています。
さらに 3 桁の `abc + cba` について、桁あふれなしの回文 output なら carry prefix が対称になることを検証し、
`196` の一段目をこの条件から排除しています。
任意個数の鏡像セルについて同じ carry 対称性を導く代数補題と、桁あふれありの回文なら最下位 output 桁が `1` になる端点条件も置いています。
さらに `add_trace` の任意長 trace をこの境界へ接続し、桁あふれなしの回文 output なら carry-in prefix が対称になることを検証しています。
この一般補題を使って `196` の一段目も排除しています。
`ReverseAddOverflowProfile.fst` は overflow の sum/carry relation を局所桁方程式へ逆向きに接続し、その relation から output 桁の pointwise 対称性を再構成します。`trace_local_palindrome_profile` は no-overflow の低桁和条件と overflow の relation 条件を一つにまとめ、回文からこの profile が必要になること、profile から output 桁対称性が得られること、profile の補集合が一段先の回文を排除することを検証します。overflow 側でも、回文必要条件を桁対称性へ戻す sound な接続を分離しています。
`trace_local_profile_complement_witness` はこの profile の補集合を、no-overflow の高い桁和または overflow relation の不成立という index付き witness へ分解します。`trace_not_local_profile_implies_witness` と `local_profile_witness_implies_not_local_profile` がこの分解の両方向を検証します。
`no_overflow_trace_outer_sum_equation` は no-overflow 段の次段外側和を現在段の外側和と境界 carry で表し、`no_overflow_outer_sum_6_to_9_implies_next_witness` は外側和 6..9 の段から次段の補集合 witness を構成します。これは 196-specific closure の一部です。
さらに、外側和 1..4 で内部に和 15 以上がある段については、`no_overflow_outer_sum_1_to_4_high_sum_15_implies_next_witness` が同じ内部セル、または overflow 時の外側 relation mismatch を次段 witness にします。
この条件を内部セルの出力 pair 和が10以上になる carry 算術へ一般化した `no_overflow_outer_sum_1_to_4_cell_implies_next_witness` と、196 の `13783 -> 52514` への適用 `local_profile_witness_52514` も検証しています。
外側和5・末尾 carry-in 1 の残る境界は、次段の隣接和 jump が12以上なら `no_overflow_outer_sum_5_carry1_jump_implies_next_witness` で no-overflow の外側和11または overflow relation mismatch に分岐できます。
overflow 段では、現在外側和10を除けば次段外側和1/11が不可能であることを `overflow_outer_sum_not_10_implies_next_outer_not_1_or_11` が示し、内部 pair 和10以上と組み合わせた `overflow_internal_cell_implies_next_witness` を `887 -> 1675` に適用しています。
外側和10の例外でも次段が no-overflow なら、`overflow_to_no_overflow_internal_cell_implies_next_witness` が内部 pair 和10以上を witness として保存し、`1067869 -> 10755470` に適用できます。
続く no-overflow 段 `10755470 -> 18211171` では、`trace_profile_facts_10755470` が固定する内部セル `i=1` を `no_overflow_outer_sum_1_to_4_cell_implies_next_witness` へ渡しています。
さらに `18211171 -> 35322452` も、内部セル `i=1` の pair 和 `15` と carry 条件を同じ補題へ渡しています。
続く `35322452 -> 60744805` では、外側和 `5`・末尾 carry-in `1` と次段 `i=2` の隣接和 `15 - 0 = 15` を固定し、同じ補題で witness を保存しています。
さらに overflow 段 `60744805 -> 111589511` では、外側和 `11` と内部セル `i=3` の `8 + 15 + 1 + 0 = 24 >= 20` を `overflow_internal_cell_implies_next_witness` へ渡しています。
続く no-overflow 段 `111589511 -> 227574622` では、外側和 `2` と内部セル `i=2` の `2 * 6 + 0 + 1 = 13 >= 10` を `no_overflow_outer_sum_1_to_4_cell_implies_next_witness` へ渡しています。
同じ no-overflow 規則で `227574622 -> 454050344` も、外側和 `4` と中央セル `i=4` の `2 * 14 + 1 + 1 = 30 >= 30` を witness にしています。
続く `454050344 -> 897100798` は外側和 `8` の no-overflow 段であり、`no_overflow_outer_sum_6_to_9_implies_next_witness` が外側セルから次段 witness を構成します。
`897100798 -> 1794102596` は overflow 外側和 `16` で、内部セル `i=1` の `18 + 16 + 1 + 1 = 36 >= 30` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `1794102596 -> 8746117567` は no-overflow 外側和 `7` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
`8746117567 -> 16403234045` は overflow 外側和 `15` で、`i=1` の `13 + 15 + 1 + 1 = 30 >= 30` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `16403234045 -> 70446464506` は no-overflow 外側和 `6` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
`70446464506 -> 130992928913` は overflow 外側和 `13` で、内部セル `i=3` の `8 + 9 + 0 + 0 = 17 >= 10` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `130992928913 -> 450822227944` は no-overflow 外側和 `4` で、内部セル `i=3` の `2 * 17 + 0 + 1 = 35 >= 30` を `no_overflow_outer_sum_1_to_4_cell_implies_next_witness` へ渡します。
続く `450822227944 -> 900544455998` は no-overflow 外側和 `8` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `900544455998 -> 1800098901007` は overflow 外側和 `17` で、内部セル `i=5` の `8 + 9 + 1 + 0 = 18 >= 10` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `1800098901007 -> 8801197801088` は no-overflow 外側和 `8` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `8801197801088 -> 17602285712176` は overflow 外側和 `16` で、内部セル `i=1` の `16 + 16 + 1 + 1 = 34 >= 30` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `17602285712176 -> 84724043932847` は no-overflow 外側和 `7` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `84724043932847 -> 159547977975595` は overflow 外側和 `15` で、内部セル `i=1` の `8 + 15 + 1 + 0 = 24 >= 20` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `159547977975595 -> 755127757721546` は no-overflow 外側和 `6` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `755127757721546 -> 1400255515443103` は overflow 外側和 `13` で、内部セル `i=6` の `14 + 14 + 1 + 1 = 30 >= 30` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `1400255515443103 -> 4413700670963144` は no-overflow 外側和 `4` で、内部セル `i=4` の `2 * 6 + 0 + 1 = 13 >= 10` を `no_overflow_outer_sum_1_to_4_cell_implies_next_witness` へ渡します。
続く `4413700670963144 -> 8827391431036288` は no-overflow 外側和 `8` から次の overflow 段へ進むため、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `8827391431036288 -> 17653692772973576` は overflow 外側和 `16` で、内部セル `i=1` の `16 + 16 + 1 + 1 = 34 >= 30` を `overflow_internal_cell_implies_next_witness` へ渡します。
続く `17653692772973576 -> 85191620502609247` は no-overflow 外側和 `7` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
続く `85191620502609247 -> 159482241005228405` は overflow 外側和 `15` で、内部セル `i=2` の `3 + 9 + 1 + 0 = 13 >= 10 + 10 * (0 + 0) = 10` を `overflow_internal_cell_implies_next_witness` へ渡しています。
続く `159482241005228405 -> 664304741147513356` は no-overflow 外側和 `6` なので、`no_overflow_outer_sum_6_to_9_implies_next_witness` を適用しています。
`reverse_trace_palindrome_cases` は任意等幅 trace の回文 output を no-overflow / overflow の二分へ分類します。
`trace_carry_obstruction` とその soundness 補題は、この二分の両方を排除する状態条件を定義します。
overflow branch には、外側桁和が `1 + 10 * carry-in` になる必要条件と、その違反を排除する補題もあります。
`trace_palindrome_obstruction` は通常の carry obstruction と overflow の和・carry obstruction を統合し、どちらからでも回文 output を排除できる soundness を持ちます。
`ReverseAddCarrySummary.fst` は、任意長の桁和列を2値carry関数の合成へ要約し、合成の単位元・結合則と `add_trace` の最終carryとの一致を検証します。これは桁数に依存しないcarry abstractionの基礎ですが、carry profile全体の対称性まではまだ要約していません。
`ReverseAddHighSum.fst` は、桁あふれなしで先行する桁和がすべて10未満なら、最初の高い桁和から carry mismatch を index 付きで導きます。さらに no-overflow の回文 output なら全桁和が10未満である必要条件と、全桁和が10未満なら output 桁が対称になる十分条件を検証します。`1675` への適用まで検証していますが、全 carry profile の対称性はまだ証明していません。
`ReverseAddWitness.fst` は、この obstruction を carry mismatch index または overflow relation mismatch index の具体 witness として扱う soundness 層です。将来の保存性証明が index を追跡できるようにします。
同ファイルの `trace_overflow_sum_jump_obstruction_at` は、隣接する桁和の差が carry 補正幅11を超えると overflow relation obstruction になる一般補題です。回文 output ではこの jump がなく、端点和は `1` または `11` に限られることも検証します。端点和がそれ以外なら index 0 の low-one obstruction へ接続します。
`trace_palindrome_candidate` は、回文 output が必ず入る no-overflow（全桁和が10未満）または overflow（端点和が11で隣接桁和の12以上の jump がない）の粗い必要条件 profile です。`trace_palindrome_implies_candidate` でこの分類を検証し、196-specific invariant の目標へ接続しています。
`trace_overflow_outer_sum_one_impossible` は、overflow candidate では対称な最終セルのため端点和 `1` が成立しないことを検証し、`trace_palindrome_candidate` の overflow 側を端点和 `11` に絞ります。
`trace_not_candidate_implies_obstruction` はこの profile の補集合を no-overflow の高い桁和、または overflow の端点/jump witness へ戻します。
`trace_candidate_complement_witness` はその branch-local witness 型を明示し、`trace_not_candidate_implies_witness` と `trace_candidate_witness_implies_obstruction` により、candidate 補集合から witness、witness から indexed obstruction への往復を検証します。
`trace_candidate_witness_implies_not_candidate` も検証し、4 branch-local witness から candidate 補集合へ戻せることを固定します。
`all_iterate_candidate_witness_from_step` と `all_iterate_candidate_witness_step_excludes_palindrome` は、一段の candidate witness 保存補題を全 iterate の回文排除へ持ち上げる接続部です。保存補題そのものはまだ 196 固有に実体化していません。
`finite_196_candidate_witness_prefix` は既存の 196 の iterate 0..6 の有限証拠をこの witness 型へ変換します。
`candidate_witness_196` は 196 の初期値からこの witness を直接構成し、`conditional_196_no_palindrome` は任意の一段保存証明を受け取って全反復の回文排除へ接続します。残る obligation はこの引数だけです。
`conditional_196_local_profile_no_palindrome` は、`trace_local_palindrome_profile` の補集合が一段保存されるという仮定を、196 の全反復における回文排除へ直接接続します。残る 196-specific obligation はこの local profile の一段 closure です。
`conditional_196_local_profile_witness_no_palindrome` は同じ接続を index付き witness の一段保存仮定へ狭めます。残る 196-specific obligation は、各 witness を一段先の witnessへ運ぶ補題です。
`trace_local_profile_witness_step_case` は、その一段保存を no-overflow 外側和6..9、低外側和の内部セル、外側和5の carry 分岐、overflow 内部セル、外側和10の no-overflow 遷移という6ケースへ分解します。`local_profile_witness_step` は既存の局所規則をこのケース契約へ束ねます。
`conditional_196_local_profile_witness_cases_no_palindrome` は、196 の全 iterate がこのケース契約を満たす仮定だけから、全反復の回文排除へ接続します。残る obligation は `forall k. trace_local_profile_witness_step_case (iterate k digits_196)` の証明です。
`all_iterate_not_candidate_excludes_palindrome` は、196 軌道の各段が candidate profile の補集合にあるという不変量から、全反復の回文到達不能性へ接続します。残る 196-specific obligation はこの補集合の全段保存です。
`all_iterate_not_candidate_step_excludes_palindrome` は、その保存条件を一段の `preserved` lemma に分解します。196-specific 作業はこの一段 closure の実体化です。
`trace_candidate_not_preserved_19` は `19 -> 110` で candidate 補集合自体も保存されないことを固定します。したがって、196 では追加の状態条件を含む closure が必要です。
`trace_no_overflow_high_sum_not_candidate` と `trace_overflow_outer_sum_not_candidate` は、candidate 補集合を高い桁和または overflow 端点条件から直接導きます。`finite_196_candidate_prefix` は 196 の iterate 0..6 についてこの profile を形式化し、high-sum、low-one、carry mismatch、outer mismatch の各 converse を実際に使用します。
`trace_no_overflow_carry_obstruction_not_candidate` は no-overflow carry mismatch witness からも candidate 補集合を直接導きます。
`trace_overflow_sum_jump_not_candidate` は、overflow branch の隣接桁和 jump を candidate 補集合へ直接接続します。`ReverseAddBoundary.fst` の `trace_profile_60744805` と `ReverseAddCEGAR.fst` の `candidate_witness_60744805_boundary` は、具体的な 196 境界 trace からこの jump witness を candidate 補集合へ戻す適用も検証します。
`trace_overflow_low_one_not_candidate` は、overflow の low-one obstruction も candidate 補集合へ接続します。これで candidate 補集合へ戻す branch-local converse は、no-overflow high-sum、overflow low-one、overflow outer、overflow jump の4種類になりました。
`candidate_boundary_sound_60744805` は、この具体 witness を candidate 非該当と indexed obstruction の両方へ接続します。
`ReverseAddBoundary.fst` は、単純 obstruction が初めて破れる `60744805` を境界回帰として検証し、旧条件が偽になること、複合 obstruction ではその reverse-add output を排除できることを確認します。
`iterate_next_obstruction_excludes_palindrome` は、任意の iterate 段について、現在段の複合 obstruction が次段の回文を排除する bridge です。
`trace_digits_equals_reverse_add` は、canonical で非空な入力について、この bridge が必要とする trace と `reverse_add` の一致を一般化します。
`finite_196_prefix_obstruction` は、その前提を `iterate 0..5` の有限 prefix で明示的に満たします。
`all_iterate_obstructions_exclude_palindrome` は、196 に限らず全 iterate 段で複合 obstruction が成立するという仮定から、次段以降の回文到達不能を帰結します。
`all_iterate_indexed_witnesses_exclude_palindrome` は、各段の mismatch index を関数 `w` で追跡する stronger な条件から同じ帰結を導きます。
`iterate_indexed_witness_excludes_palindrome` は、その条件を一段ごとの有限 bridge として切り出します。
`trace_palindrome_obstruction_at_exists` と `all_iterate_obstructions_have_indexed_witnesses` は、複合 obstruction から各段の index witness の存在を導きます。
`trace_overflow_outer_obstruction_at_sound` は、overflow時の端点和条件違反を index 0 の具体 witness へ持ち上げます。将来の196-specific invariantで、overflow branchを端点条件として扱うための接続です。
`all_iterate_existential_witnesses_exclude_palindrome` は、関数選択なしに各段の existential witness だけから次段の回文を排除します。
`iterate_obstruction_from_step` と `all_iterate_obstructions_from_step` は、各段で existential obstruction が一段先へ保存されるという単一の仮定を全反復へ持ち上げます。`all_iterate_obstruction_step_excludes_palindrome` は、このclosure条件を既存の回文排除bridgeへ接続します。
`trace_palindrome_obstruction_exists_not_preserved_19` は、`19 -> 110` でこのclosureが失敗することを固定し、単純な obstruction の再利用ではないことを検証します。
`trace_palindrome_obstruction_exists_not_preserved_11_1199` は、11の倍数でも `1199 -> 11110 -> 12221` で同じclosureが失敗することを固定します。したがって、196で成立する11倍数不変量だけでは不足します。
`witness_index_196` は確認済み prefix の witness index を関数化し、`finite_196_indexed_nonpalindrome`（`iterate 1..7`）と `finite_196_suffix_indexed_nonpalindrome`（`iterate 8..30`）へ接続します。`finite_196_prefix_nonpalindrome` が両方を結合し、`iterate 12` の `60744805` 以降も overflow/no-overflow の局所 witness を明示します。
この全段 obstruction の保存自体は、196 についてまだ証明していません。
`trace_palindrome_obstruction_not_inductive_19` は、obstruction 単体をそのまま inductive invariant にできない境界例 `19 -> 110 -> 121` を固定します。
overflow 側の `887 -> 1675` と `7436 -> 13783` は最下位桁条件で、続く `1675 -> 7436` は carry prefix の非対称性で排除しています。
さらに `7436 -> 13783 -> 52514 -> 94039 -> 187088 -> 1067869 -> 10755470 -> 18211171 -> 35322452 -> 60744805 -> 111589511 -> 227574622 -> 454050344 -> 897100798 -> 1794102596 -> 8746117567 -> 16403234045 -> 70446464506 -> 130992928913 -> 450822227944 -> 900544455998 -> 1800098901007 -> 8801197801088 -> 17602285712176 -> 84724043932847 -> 159547977975595 -> 755127757721546 -> 1400255515443103` の各遷移と、iterate 29 までの trace obstruction を検証し、`iterate 30 digits_196 == digits_1400255515443103` まで有限 prefix を延長しています。`finite_196_prefix_nonpalindrome` は `iterate 1..30` の各状態が回文でないことを一つの bounded lemma にまとめています。

`AbstractReachability.fst` は、`0 <= state < count` の有限状態グラフに対して、
燃料の範囲で到達集合を計算し、追加がなくなれば固定点として扱います。
燃料が尽きた場合は `Unknown` とし、`Unreachable states` を返した場合の
`check_bad_sound` を F* で証明しています。`check_bad_fuel` で bounded CEGAR
試行も実行できます。
`reverse_edge`、`predecessors`、`closure_reverse` も備え、target からの逆向き探索を
`backward_checker_sound` で sound に扱えます。
`invariant_on_closure` と `invariant_excludes_bad` は、有限 fuel に依存しない
invariant proof の入口です。
`AbstractReachabilityExample.fst` には小さな到達/到達不能グラフを置いています。
`ReverseAddResidue.fst` は `value mod m` の最初の抽象です。
edge を universal にしているため sound ですが粗く、到達不能性を証明する用途にはまだ使いません。
`ReverseAddModPair.fst` は `value mod m` と
`value (reverse_digits xs) mod m` のペアを `m^2` 状態へ写します。
具体的な一段遷移が抽象 edge に含まれること、palindrome が抽象 bad 状態へ写ること、
その抽象 checker の `Unreachable` 結果が concrete の反例を排除することを証明しています。
また、pair state から residue state への射影と concrete abstraction の整合性も証明しています。
ただし、これはまだ 196 の到達不能性を返す抽象としては精密さを確認していません。
`ReverseAddBlockCarry.fst` は `m` 幅の residue block と、その block sum の carry を
`2*m^2` 状態へ符号化します。source/target の carry 整合性を edge に含め、
concrete transition と palindrome predicate の soundness を証明しています。
`m=b^k` と選べば、これは k 桁ブロックの carry 抽象として利用できます。
`ReverseAdd196.fst` では base 10 の 196 に対し、`m=2` の粗い抽象が
concrete の `196 -> 887` とは異なる abstract bad successor を許すことを証明しています。
これは抽象 counterexample としての CEGAR 入力です。
`ReverseAddFixedWidth.fst` は width を引数に取り、`10^width` 未満の canonical value を
exact state、その他を fallback へ写す一般の桁幅 refinement です。concrete transition と
palindrome soundness、checker の unreachable soundness を検証しています。
`power10 width > 887` の場合に 196 の一段目が bad にならないことも width-parametric に検証します。
`ReverseAddInvariant.fst` は、空でない canonical numeral について reverse-and-add の値が
1 段で厳密に増加することを検証します。これは無限状態での不変量証明に使える補題ですが、
反復結果の canonical 性・非空性と、任意の正の反復回数での値の狭義増加も検証します。
さらに 7436 以降の 196 軌道が 11 の倍数であることを、交代和を使って不変量化します。
`divisible_196_by_11_after_iterate_3` は iterate shift を別抽象にせず、3段目を基点に帰納して `iterate (k+3) digits_196` へこの不変量を直接接続します。
ただし 11 の倍数だけでは回文を排除できないことも補題で確認しています。
`iterate_value_at_least` と `fixed_width_fallback_reached` は、strict increase により任意の固定幅で軌道が fallback へ到達することを検証します。したがって、fallbackをbadとする有限 FixedWidth checkerだけでは、196の無限軌道を証明できません。
196 の palindrome 到達不能性そのものはまだ証明していません。
`ReverseAddFixed3.fst` はその width=3 wrapper で、196 の一段目では bad state に到達しません。
`ReverseAddRefinedProduct.fst` は fixed3 情報と block-carry state の積を取り、
block projection、transition soundness、palindrome soundness を保持します。
`ReverseAddCEGAR.fst` は stage 列を走査し、abstract `Reachable` の最初の bad state を
counterexample として次の stage へ渡します。現在は `BlockCarry -> ProductOneStep` の
2 stage loop を実装し、product stage で `Unknown` を返すところまでです。
stage の counterexample と探索済み集合に bad がないという分類も F* で sound に取り出せます。
stage API には `FixedWidth (width, fuel)` もあり、桁幅と bounded 探索深さを差し替えられます。
`ReverseAddPredecessor.fst` は `0..value y` を調べる bounded predecessor 列挙です。
候補の soundness と、canonical な concrete predecessor の completeness を証明しています。

## 検証

```sh
make verify
```

既定値はこの環境の F* (`$HOME/.everest/FStar`) と Z3 4.15.4 です。
F* が要求する Z3 4.13.3 を使う場合は、`z3-4.13.3` が PATH にある状態で次を実行します。

```sh
FSTAR_Z3_VERSION=4.13.3 make verify
```

`iterate 37 -> 38 -> 39 -> 40 -> 41 -> 42 -> 43 -> 44 -> 45 -> 46 -> 47 -> 48 -> 49 -> 50` も具体的な遷移と local-profile witness を検証しています。38 以降は concrete trace の case 契約を直接検証し、50 まで有限 prefix を延長しています。

この段階では、桁幅 stage を自動生成する汎用 CEGAR と、196 の無限到達不能性定理は未実装です。
