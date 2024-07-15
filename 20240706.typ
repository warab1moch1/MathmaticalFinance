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
  title: "No.7",
  authors: (
    "warab1moch1",
  ),
  url: "https://github.com/warab1moch1"
)

#set math.equation(numbering: "(1)")

= 測度変換

#theorem[
  #h(1mm) Levyの定理\
  $M$ : $cal(F)_t$ マルチンゲールで $M_0=0$\
  $angle.l M angle.r_t = t$

  $M$ : $(cal(F)_t)$ - BM
]
#proof[
  $f(t, x) := exp(i alpha x + 1/2 alpha^2 t) quad (alpha in.small RR)$
  とおくと#footnote[連続セミマルチンゲールとして$t$を扱うことを明記]
  $ f_x = i alpha f $
  $ f_(x x) = - alpha^2 f $
  $ f_t = 1/2 alpha^2 f $
  Ito fomula 
  $ f(t, M_t) &= f(0, M_0) + integral_0^t f_t (s, M_s) d s \
  &quad + integral_0^t f_x (s, M_s) d M_s + integral_0^t 1/2 f_(x x) (s, M_s) d s\
  &= 1 + i alpha integral_0^t f_x (s, M_s) d M_s $
  martingale.

$ therefore #h(1mm) EE[e^(i alpha M_t + 1/2 alpha^2 t)|cal(F)_s] = e^(i alpha M_s + 1/2 alpha^2 s) $
両辺に$e^(- i alpha M_s - 1/2 alpha^2 t)$ : $cal(F)_s$ 可測
$ EE[e^(i alpha (M_t - M_s))|cal(F)_s] = e^(- 1/2 alpha^2 (t-s)) $
Tower Law
$ EE[e^(i alpha (M_t - M_s))] &= EE[e^(i alpha (M_t - M_s))|cal(F)_s]\
&= EE[e^(- 1/2 alpha^2 (t-s))]\
&= e^(- 1/2 alpha^2 (t-s)) $ <ref>
$ therefore M_t - M_s tilde.op cal(N) (0, t-s) $
#footnote[$cal(N)(0, sigma^2)$の特性関数$EE[e^(i t X)] = e^(-1/2 sigma^2 t^2)$]

next, $(cal(F)_t)$ - 独立増分性

$forall A in.small cal(F)_s quad C in.small BB(RR)$
$ PP({M_t - M_s in.small C} sect A) = PP({M_t - M_s in.small C}) PP(A) $
$PP(A) = 0$の時自明、$PP(A) > 0$に興味あり
$ PP_A (B) := PP(A sect B) / PP(A) $
新しい確率測度を導入する。

$ EE[bold(1)_A e^(i alpha (M_t - M_s))] &= EE[EE[bold(1)_A e^(i alpha (M_t - M_s))|cal(F)_s]]\
&= EE[bold(1)_A EE[e^(i alpha (M_t - M_s))|cal(F)_s]] quad #text(0.8em)[($because$ $A in.small cal(F)_s$)] \
&= EE[bold(1)_A e^(- 1/2 alpha^2 (t - s))] quad #text(0.8em)[($because$ @ref )]\
&= EE[bold(1)_A] e^(- 1/2 alpha^2 (t - s)) \
&= PP(A) e^(- 1/2 alpha^2 (t - s)) $

#lemma[$f$ : $PP$ - 可積分 
$ EE^(P_A)[f] = EE[bold(1)_A f] / PP(A) $]
#proof[
  簡単のため、指標関数の時のみ示す。以降は standard-machine に従うと考えればよい。
  $f = bold(1)_B$ のとき、確率の定義から
  $ EE^(P_A)[bold(1)_B] &= integral_Omega bold(1)_B d PP_A (omega)\
  &= integral_B 1 d PP_A (omega)\
  &= PP_A (B)\
  &= PP(A sect B) / PP(A) \
  &= EE[bold(1)_A bold(1)_B] / PP(A) $
]
上の補題より、次が従う。
$ EE^(P_A)[e^(i alpha (M_t - M_s))] = e^(- 1/2 alpha^2 (t - s)) $
すると、$M_t - M_s$ の分布は $PP$ 上でも $PP^(P_A)$ 上でも変わらないことがわかる。
これより、
$ therefore PP({M_t - M_s in.small C} sect A) / PP(A) = PP({M_t - M_s in.small C}) $
よって
$ M_t - M_s bot cal(F)_s $
]

== Radon-Nikodym 微分
いま、$Omega$ 上に確率測度 $PP$、$QQ$ があり、同値とする#footnote[$ forall A in.small F quad PP(A) = 0 arrow.l.r.double QQ(A) = 0 $]。
このとき、ある $ D in.small L^1 (Omega, cal(F), PP) $ が存在して
$ QQ(A) = EE^PP [D A] $
を満足する。

これを、$QQ$ の $PP$ による Radon-Nikodym 微分と言い、$(d QQ)/(d PP)$ で表す。
#example[
  $Omega = [0, 1]$
  $ PP([a, b]) = b - a $
  $ QQ([a, b]) = b^2 - a^2 $
  とする。このとき $x in.small Omega$
  $ PP([x, x + Delta x]) = Delta x $
  $ QQ([x, x + Delta x]) = Delta x^2 + 2 Delta x dot.op x $
  $ therefore QQ([x, x + Delta x]) / PP([x, x + Delta x]) &= Delta x + 2 x\
  &tilde.eq 2 x $
  となっていることがわかる。これより、
  $ EE^PP [2x, [a, b]] &= integral_a^b 2x d PP(x)\
  &= [x^2]_a^b\
  &= b^2 - a^2\
  &= QQ([a, b]) $
  $ therefore #h(1mm) (d QQ)/(d PP) (omega) = 2 omega $
  であるから、$(d QQ)/(d PP)$ は測度が何倍の密度を持っているかを表現している。
]

いま、次のような確率過程 ( Density process ) を考える。
$ D_t := EE^PP [(d QQ)/(d PP)|cal(F)_t] $
定義より、上の確率変数 $(d QQ)/(d PP)$ に対して、$PP$ における条件付期待値を考えていることがわかる。

fact
[$D_t$ の性質 #v(1mm)
  -- マルチンゲール#v(1mm)
    定義より、条件付期待値の Tower Law から従う。#v(1mm) 
  -- $ attach(inf, b:t>=0) D_t >= 0 $
  として $(PP $ - $a.s. #h(1mm) omega)$ にとれる、即ち
  $ PP(A) = 0 arrow.l.r.double QQ(A) = 0 $
  でない点は可算個程度しかない。#v(1mm)
  -- もし、$D_t$ を連続過程としてとれるなら、
  $L$ : 連続過程として
  $ D_t = cal(E) (L)_t $
  として、stochastic exponential の形で表せる#footnote[次節では、この事実を逆引き的に用いる。]。
]#v(1mm)
これらの性質と定義から、次が従う。#v(1mm)
#enum(
  enum.item()[$EE^QQ [X] = EE^PP [X D]$#v(1mm)
  $ because #h(1mm) EE^QQ [X] &= integral_Omega X(omega) d QQ(omega)\
  &= integral_Omega X(omega) (d QQ)/(d PP) d PP(omega)\
  &= EE^PP [X (d QQ)/(d PP)] $
  ],
  enum.item()[$X_t$ : $cal(F)_t$ 可測であるとき、 $EE^QQ [X_t] = EE^PP [X_t D_t]$ #v(1mm)
  $ because #h(1mm) EE^QQ [X_t] &= EE^PP [X_t D]\
  &= EE^PP [EE^PP [X_t D|cal(F)_t]] quad #text(0.8em)[($because$ Tower Law)]\
  &= EE^PP [X_t EE^PP [D|cal(F)_t]]\
  &= EE^PP [X_t D_t] quad #text(0.8em)[($because$ $D_t$ のマルチンゲール性)] $],
  enum.item()[$X_t$ : $cal(F)_t$ 可測であるとき、$EE^QQ [X_t|cal(F)_s] = D_s^(-1) EE^PP [X_t D_t|cal(F)_s] quad (s<= t)$#v(1mm)
  $because$ 右辺が、（左辺を条件付期待値たらしめる）部分平均の性質を満たしていればよく、\
  $forall A in.small cal(F)_s$ に対し、
  $ integral_A D_s^(-1) EE^PP [X_t D_t|cal(F)_s] &= integral_Omega bold(1)_A EE^PP [X_t D_t|cal(F)_s] D_s^(-1) d QQ\
  &quad #text(0.8em)[上の2より、#h(1mm) $EE^QQ [X_t / D_t] = EE^PP [X_t] $]\
  &= integral_Omega underbrace(bold(1)_A EE^PP [X_t D_t|cal(F)_s], cal(F)_s "可測") d PP\
  &= EE^PP [EE^PP [bold(1)_A X_t D_t|cal(F)_s]]\
  &= EE^PP [bold(1)_A X_t D_t]\
  &quad #text(0.8em)[$bold(1)_A X_t D_t$ は $cal(F)_t$ 可測であることに注意すれば、]\
  &= EE^QQ [bold(1)_A X_t] quad #text(0.8em)[($because$ 2より、#h(1mm) $ EE^PP [X_t D_t] = EE^QQ [X_t]$)]\
  &= EE^QQ [X_t, A] $
  これより、右辺は正に $QQ$ の下での部分平均となっており、所望の結果である。]
)

== Gilsanov の定理
いま、次のような確率過程を考える。
$ L_t := integral_0^t theta_s d W_s $
この $L_t$ を用いた次のような stochastic exponential を考えると、伊藤の等長性から
$ cal(E) (-L)_t &= exp(-L_t - 1/2 angle.l L angle.r_t)\
&= exp(-integral_0^t theta_s d W_s - 1/2integral_0^t theta_s^2 d s) $
このとき、Radon-Nykodim微分における fact(後で上手く引用する形で記述する) から、この $cal(E)(-L)_t$ を Density Process に持つような $QQ$ について考える。\
実際、$forall A in.small cal(F)$ について
$ QQ(A) = integral_A cal(E)(-L)_infinity d PP $
とすればよい#footnote[
  #theorem[
    $M$ : 一様可積分マルチンゲールであるとき、\
    $M_t$ から $M_infinity$ ( $L^1$ 収束かつ概収束) かつ $EE[M_infinity|cal(F)_t] = M_t$
    なる $M_infinity$ の存在が言える。\
    マルチンゲール収束定理*（要調査）*
  ]
  一般に、$L^2$ 有界マルチンゲール  ($attach(sup, b:t>0) EE[M_t^2] < infinity$) $arrow.r.double$ 一様可積分マルチンゲール $arrow.r.double$ $L^1$ 有界マルチンゲール という関係性が成立している。\
  ブラウン運動 $W$ は $sup EE[W_t^2] = t arrow.r infinity$ であることに注意。
]。
#pagebreak()
すなわち、
$ (d QQ)/(d PP) = cal(E)(-L)_infinity $
であり、Density Process $D_t$ の一般形は
$ D_t &= EE^PP [(d QQ)/(d PP)|cal(F)_t]\
&= EE^PP [cal(E)(L)_infinity|cal(F)_t]\
&= cal(E)(-L)_t $
とすればよい。このとき、$cal(E)(-L)_infinity$ が存在するための十分条件は
$ EE^PP [e^(1/2integral_0^T theta_s^2 d s)] < infinity $
であり、これを Novikov 条件という。これは、$cal(E)(-L)_t$ の指数部分の正規性と $L^2$ 有界性に関する条件である。

#theorem[#h(1mm) Gilsanov の定理\
$(theta_t)$ から新たな（確率）測度 $QQ$ を作ることを考える。\
ここで、ブラウン運動 $W$ : $PP$ - BM とすると $ W_t^QQ := W_t + integral_0^t theta_s d s $ <W_tQQ>
によって定義された $W_t^QQ$ は $QQ$ - BM である。
] 
このとき、@W_tQQ の微分形は
$ d W_t^QQ = d W_t + theta_t d t $
であることに注意する。

このとき、実際に $W_t^QQ$ が $QQ$ - BM であることを示すには、*Levy* の定理から(記号)#v(1mm)
-- $0$ スタート #v(1mm)
-- $QQ$ - マルチンゲール #v(1mm)
-- 2次変分 $t$ #v(1mm)
であればよい。

表式から、$0$ スタートは自明に従う。また、2次変分も
$ d W_t^QQ d W_t^QQ &= (d W_t + d t)^2\
&= d W_t d W_t\
&= d t $
より確認できる。

ここで、$QQ$ - マルチンゲールについては
$ D_t = cal(E)(-L)_t $
より、
$ (d cal(E)(-L)_t)/(d (-L)_t) = cal(E)(-L)_t $
であるから、
$ d D_t &= d cal(E) (-L)_t\
&= cal(E)(-L)_t d(-L)_t\
&= - D_t d L_t\
&= - D_t theta_t d W_t $
これから、$PP$ 上で
$ d (W_t^QQ D_t) &= W_t^QQ d D_t + D_t d W_t^QQ + d D_t d W_t^QQ\
&= - W_t^QQ D_t theta_t d W_t + D_t (d W_t + theta_t d t) - D_t theta_t d t\
&= (1 - W_t^QQ theta_t) D_t d W_t $
$ therefore #h(1mm) W_t^QQ D_t : PP "- マルチンゲール" $
ここで、測度の変換に際し
$ EE^QQ [X_t|cal(F)_s] = D_s^(-1)  EE^PP [X_t D_t|cal(F)_s] $
が成立しているのであったから
$ EE^QQ [W_t^QQ|cal(F)_s] &= D_s^(-1) EE^PP [W_t^QQ D_t|cal(F)_s]\
&= D_s^(-1) W_s^QQ D_s\
&= W_s^QQ $
$ therefore #h(1mm) W_t^QQ : QQ "- マルチンゲール" $
となり、所望の結果を得る。

これまでに得られた結果を踏まえると、$cal(E)(-L)_t$ による Gilsanov 変換は、#v(1mm)
-- $M$ : $PP$ - 局所マルチンゲール#v(1mm)
から#v(1mm)
-- $M + angle.l M, L angle.r$ : $QQ$ - 局所マルチンゲール#v(1mm)
を得るための操作であると言い換えられる。

実際、
$ d W_t^QQ = d W_t + theta_t d t $
とすることで、
$ d X_t = mu_t d t + sigma_t d W_t "on" PP $
$ d X_t = (mu_t - theta_t sigma_t) d t + sigma_t d W_t "on" QQ $
であることから、確率測度 $QQ$ を（適当に）取り換えればドリフト項が何にでもなることがわかる。

fact[#h(1mm)マルチンゲール表現定理\ 
  completed Brownian filtration $(attach(cal(F)_t, t:tilde.op))$ 上において
  $M$ : 連続マルチンゲールとする。\
  このとき、$C in.small RR$ で
  $ M_t = C + integral_0^t h_s d W_s $
  と、ある $h$ によって書ける。\
  あるいは、一般に、マルチンゲール $M$ に対し
  $ d M_t = h_t d W_t $
  と書ける。
]

これより、$N$ : 連続マルチンゲールのとき
$ d N_t = sigma_t d W_t quad (sigma_t eq.not 0) $
として
$ M_t = C + integral_0^t phi_s d N_s $
なる $phi$ が存在する。というのは、
$ d M_t &= h_t d W_t\
&= (h_t sigma_t^(-1)) sigma_t d W_t\
&= (h_t sigma_t^(-1)) d N_t $
とできるからである。




いま、割引株価過程
$ Z_t := B_t^(-1) S_t $
$ d B_t &= - B_t^(-2) d B_t\
&= - r B_t^(-1) d t $
$ d Z_t &= B_t^(-1) d S_t + d B_t^(-1) S_t\
&= B_t^(-1) {d S_t + (- r d t) S_t}\
&= B_t^(-1) {S_t (mu d t + sigma d W_t - r d t)}\
&= Z_t {(mu - r) d t + sigma d W_t} $
$theta = (mu - r)/sigma$ Gilsanov
$ d W_t^QQ = d W_t + theta d t $
$ d Z_t = Z_t sigma d W_t^QQ $

$ E_t := EE^QQ [B_T^(-1) X|cal(F)_t] $

$ d E_t = phi_t d Z_t $
$ psi_t := E_t - phi_t Z_t $
$(phi, psi)$

1. $(phi, psi)$
3. $ V_t &= phi_t S_t + psi_t B_t\
&= phi_t S_t + (E_t - phi_t Z_t) B_t\
&= B_t E_t $
$ therefore #h(1mm) V_T &= B_T EE^QQ [B_t^(-1) X|cal(F)_T]\
&= B_T B_T^(-1) X \
&= X $
2. $ d V_t &= E_t d B_t + B_t d E_t + d E_t d B_t\
&= (phi_t Z_t + psi_t) d B_t + B_t (phi_t d Z_t) + d B_t (phi_t d Z_t)\
&= phi_t (Z_t d B_t + B_t d Z_t + d B_t + d Z_t) + psi_t d B_t\
&= phi_t d (B_t Z_t) + psi_t d B_t\
&= phi_t d S_t + psi_t d B_t $

#corollary[
  #h(1mm) デリバティブ価格公式#v(1mm)
  $ V_t &= B_t E_t\
  &= B_t EE^QQ [B_T^(-1) X|cal(F)_t] $
]

