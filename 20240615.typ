#import "manual_template.typ": *
#import "theorems.typ": *
#show: thmrules

// Define theorem environments

#let theorem = thmbox(
  "theorem",
  "Theorem",
  fill: rgb("#e8e8f8")
)
#let lemma = thmbox(
  "theorem",            // Lemmas use the same counter as Theorems
  "Lemma",
  fill: rgb("#efe6ff")
)
#let corollary = thmbox(
  "corollary",
  "Corollary",
  base: "theorem",      // Corollaries are 'attached' to Theorems
  fill: rgb("#f8e8e8")
)

#let definition = thmbox(
  "definition",         // Definitions use their own counter
  "Definition",
  fill: rgb("#e8f8e8")
)

#let exercise = thmbox(
  "exercise",
  "Exercise",
  stroke: rgb("#ffaaaa") + 1pt,
  base: none,           // Unattached: count globally
).with(numbering: "I")  // Use Roman numerals

// Examples and remarks are not numbered
#let example = thmplain("example", "Example").with(numbering: none)
#let remark = thmplain(
  "remark",
  "Remark",
  inset: 0em
).with(numbering: none)

// Proofs are attached to theorems, although they are not numbered
#let proof = thmproof(
  "proof",
  "Proof",
  base: "theorem",
)

#let solution = thmplain(
  "solution",
  "Solution",
  base: "exercise",
  inset: 0em,
).with(numbering: none)

#let project(title: "", authors: (), url: "", body) = {
  set page(paper: "a4", numbering: "1", number-align: center)
  set document(author: authors, title: title)
  set text(font: "Linux Libertine", lang: "en")
  set heading(numbering: "1.1.")
  set par(justify: true)
  set list(marker: ([•], [--]))
  show heading: it => pad(bottom: 0.5em, it)
  show raw.where(block: true): it => pad(left: 4em, it)
  show link: it => underline(text(fill: blue, it))


  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  pad(
    top: 0.5em,
    bottom: 2em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center)[
        #author \
        #link(url)
      ]),
    ),
  )

  outline(indent: true)

  v(2em)

  body
}

#show: project.with(
  title: "No.6",
  authors: (
    "warab1moch1",
  ),
  url: "https://github.com/warab1moch1"
)


= 停止時刻

$(Omega, cal(F), PP, cal(F)_t)$ : filtrated Probability Space であるとする。

#definition[#h(1mm)停止時刻\
$T$ : $Omega arrow.r [0, infinity]$#footnote[
  $infinity$ を含むことに注意
] が停止時刻であるとは、$T$ が確率変数であって、かつ
$ forall t >= 0 quad {T <= t} in.small cal(F)_t $
であることをいう。
ここで、${T <= t} = {omega in.small Omega|T(omega) <= t}$ である。

このとき、
$ cal(F)_t := {A in.small cal(F)|forall t >= 0 quad A sect {T <= t} in.small cal(F)_t} $
を（停止）時刻 $T$ での情報系（$sigma$ - 加法族）という。 
]

このときの直観的な解釈としては、#v(1mm)
-- $T$ はランダムな時刻である\
定義より、
$ T : Omega arrow.r [0, infinity] $
である確率変数であり、（上での表記の通り）時刻 $T$ 自体はあるランダムネスの素 $omega$ に基づいている。#v(1mm)
-- 停止時刻の意味合い\
確率変数であるということに加え、更に
$ {T <= t} in.small cal(F)_t (forall t >= 0) $
である。これは、『未来の情報を使わずに決めることの時刻』であることを意味している。卑近な例としては、#v(1mm)
- 所持金が初めて1万円を割る時刻 $T$
当然ではあるが、これは、その瞬間（割ったタイミング）にしかわからないため、停止時刻である条件を満たしている。

逆に、そうでない例としては#v(1mm)
- いずれ1万円を割るなら $0$、それ以外なら $100$ として定めた時刻 $S$
これは、未来の情報（条件）を使っていることから停止時刻でない。

#example[#h(1mm)今後の考察の対象\
  -- $T equiv s$ : 定数時刻\
  #proof[
    $ {T <= t} &attach(eq, t: "def") {s <= t}\
    &= cases(
      Omega quad (s<= t),
      nothing quad (s > t)
    ) in.small cal(F)_t
  $
  ]
  -- $T,#h(1mm) S$ : 停止時刻であるとき、$T + S$、$min(T, S)$
  #proof[
    $ {(T and S) <= t}#footnote[
      $ T and S := min(T, S) $
    ] = {T <= t} union {S <= t} $
    であり、$T, S$ がいずれも停止時刻であるという仮定から
    $ {T <= t},#h(1mm) {S <= t} in.small cal(F)_t $
    であり、その有限和もまた $in.small cal(F)_t$ である。
  ]
  このように、標準的な演算は（おおよそ）停止時刻になることがわかる。

  -- $F subset.eq RR$ : 閉（開）集合、$X_t$ : 連続確率過程のとき、
  $ H := inf{t >= 0|X_t in.small F} $
  即ち、$F$ への到達時刻 $H$ ( Hitting time ) は停止時刻#footnote[
    $min$ でなく、$inf$ としている理由は開集合としている場合でも絶対に存在するためである
  ]である。
]

#definition[#h(1mm)任意抽出定理 ( Optional sampling theorem )\
  $M$ : マルチンゲール（右連続）、
  $S,#h(1mm) T$ : 有界な停止時刻 ( $S <= T$ ) とする。
  即ち、
  $ exists N("定数") quad S, #h(1mm) T <= N $
  であり、また
  $ forall omega in.small Omega quad S(omega) <= T(omega) $
  である。このとき、
  $ EE[M_T|cal(F)_s] = M_S $
  である。 ここで、$M_t$ : 確率変数であり、
  $ M_T (omega) := M_T(omega) (omega) $
  である。#footnote[
    仮定 $S <= T$ がないとき、（一般に）
    $ EE[M_T|cal(F)_S] = M_(T and S) $
    である。
  ]
]

次に、停止時刻での情報系についてその意味合いや応用例を取り上げる。

これまでに取り上げてきた定数 $t$ での $cal(F)_t$ と、（繰り返しにはなるが）確率変数である停止時刻によって得られる情報系 $cal(F)_T$ とを区別することが肝要である。

-- $X_t$ : $cal(F)_t$ - 可測であるとき、
$X_T$ : $cal(F)_T$ - 可測である。
ここで、
$ X_T(omega) = X_T(omega) (omega) bold(1)_{T eq.not infinity} (omega) $
である。即ち、$T$ が無限であるときは考えていない。

-- $X$ : 連続、かつ $X_t$ : $cal(F)_t$ - 可測であるとき、
$ X_t^T := X_(t and T) $
即ち、$T$ で停止した（動きを凍結させた）確率過程を考える。\
（確率変数 $X^T$ : 連続、また 確率過程 $X_t^T$ : $cal(F)_t$ - 可測）

このとき、$X$ : 右連続マルチンゲールであるなら、$X_t^T$ : 右連続マルチンゲールが従う。
#proof[$s <= t$ において、
  $ EE[X_t^T|cal(F)_s] &= EE[X_(t and T)|cal(F)_s] quad #text(0.8em)[($because$ 上の定義)]\
&= X_(t and T and s) quad #text(0.8em)[($because$ 任意抽出定理)]\
&= X_(s and T)\
&= X_s^T $
ここで、停止時刻の例で取り上げたように、定数 $s,#h(1mm) t$ : 停止時刻であり、またそれ（ら）と停止時刻 $T$ との最小値もまた停止時刻であることに注意する。これより、上のように任意抽出定理を用いることができる。
]

= 反射原理

*図*
#theorem[#h(1mm)反射原理
  $W$ : ブラウン運動とする。このとき、$a$ への到達時刻
$ T_a := inf{t >= 0|W_t = a} $
に加え、$W$ の最大値過程
$ S_t := sup_(0<=s<=t) W_s $
を考える。このとき、
$ PP(S_t >= a,#h(1mm) W_t <= b) = PP(W_t >= 2 a - b) quad (a >= b >= 0) $
が成立している。]

ここで、
\# fact

$B_t := W_(T_a + t) - W_(T_a)$
はブラウン運動である（強マルコフ性）
↑（ここまで）

これは、ブラウン運動の定義である独立増分性より、
$ W_(t+s) - W_s $
がまたブラウン運動であることを考えると、この $s$ が stopping time $T_a$ であっても大丈夫であることを意味している。

また、最大値過程 $S_t$ : $cal(F)_t$ - 可測である。

#proof[
  $ PP(S_t > a,#h(1mm) W_t <= b) &= PP(T_a <= t, W_t <= b)\
  & #text(0.8em)[$paren.l$ $because$ $t$ までの最大値が $a$ 以上] \ 
  & #text(0.8em)[$arrow.r.double$ $t$ までに Hitting time $T_a$ が来ているはず $paren.r$]\
  &= PP(T_a <= t,#h(1mm) B_(t - T_a) <= b - a) quad #text(0.8em)[($because$ $B_(t - T_a) = W_t - W_(T_a) = W_t - a)$#footnote[
    $W_t$ は連続かつ1点集合 $a$ は閉であるため、停止時刻 $T_a$ でまさに値 $a$ をとる。
  ]]\
  &= PP^T_a times.circle cal(W) ({(s, omega) in.small RR times C(bracket.l 0, infinity paren.r)|s <= t,#h(1mm) omega(t-s) <= b - a})\
  &= PP(T_a <= t,#h(1mm) B_(t- T_a) >= a - b) quad #text(0.8em)[($because$ ブラウン運動の正規性#footnote[
    $X tilde.op cal(N)$ のとき、分布の対称性から $PP(X <= alpha) = PP(X >= - alpha)$ が従う。
  ])]\ 
  &= PP(T_a <= t, #h(1mm) W_t >= 2 a - b)\
  &= PP(W_t >= 2 a - b) $
  最後の変形に関しては、
  $a >= b$ から
  $ W_t &>= 2 a - b\
  &>= 2 a - a\
  &= a $
  より、上での Hitting time の論理から $T_a <= t$ が保証されていることによる。
]

これより、何が嬉しいか（*Shreve p.111 を参照*）







