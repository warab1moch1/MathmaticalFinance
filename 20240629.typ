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
  title: "No.8",
  authors: (
    "warab1moch1",
  ),
  url: "https://github.com/warab1moch1"
)

= 伊藤の補題

No.7 で導入した確率積分により、次を得たことを思い出す。

#lemma[
  #h(1mm)伊藤の補題
  $ d f(X^1, dots.c , X^n) = sum_i (diff f) / (diff x_i) (X^1, dots.c , X^n) d X^i + 1 / 2 sum_i sum_j (diff f) / (diff x_i diff x_j) (X^1, dots.c , X^n) d X^i d X^j $
  上の微分形は、積分形を天下り的に表現したものである。即ち、
  $ f(X_t^1, dots.c , X_t^n) &= f(X_0^1, dots.c , X_0^n)\
  &quad + sum_i integral_0^t (diff f) / (diff x_i) (X_s^1, dots.c , X_s^n) d X_s^i\
  &quad + 1 / 2 sum_i sum_j integral_0^t (diff f) / (diff x_i diff x_j) (X_s^1, dots.c , X_s^n) d angle.l X^i X^j angle.r $
  が真の姿であることに注意する。
]

これより、伊藤の補題（公式）を実際に使用してみる。典型的な例としては、

1. $f(x) = x^n$ のとき
$ f^prime (x) &= n x^(n-1)\
f^(prime prime)(x) &= n (n-1) x^(n-2) $
であるから、1変数の時を考えて
$ d f(X_t) = f^prime (X_t) d X_t + 1/2 f^(prime prime) (X_t) d X_t d X_t $
$ d (X_t^n) = n X_t^(n-1) d X_t + n (n-1) X_t^(n-2) d X_t d X_t $
#example[\
  $ f(x) = x^2$ で $X=W$ のとき（即ち $X$ は Brownian Motion）
  $ d(W_t^2) &= 2 W_t d W_t + 1/2 dot.op 2 dot.op 1 d W_t d W_t\
  &= 2 W_t d W_t + 1 d t $
  $ therefore d (W_t^2 - t) = 2 W_t d W_t $
  これを積分して、
  $ (W_t^2 - t) = (W_0^2 - 0) + integral_0^t 2 W_s d W_s $
  $ therefore W_t^2 - t = 2 integral_0^t W_s d W_s  $
  ここで、左辺がマルチンゲールであることを以前確認したが、確かに右辺が確率積分となっていることから整合的である。
  
  また、そのマルチンゲール性から2次変分の形がわかる。
]

2. $f(x) = e^x$ のとき
$ f^prime (x) = f^(prime prime) (x) = e^x #h(3mm) (= f (x)) $
であるから、
$ d (e^(X_t)) &= e^(X_t) d X_t + 1/2 e^X_t d X_t d X_t\
&= e^(X_t) (d X_t + 1/2 d X_t d X_t) $

3. $f(x) = log x$ のとき
$ f^prime (x) = 1 / x $
$ f^(prime prime) (x) = - 1 / x^2 $
であるから、
$ d(log X_t) = (d X_t) / X_t - (d X_t d X_t) / (2 X_t^2) $

4. $f(x, y) = x y $ のとき
$ f_x (x, y) = y quad f_y (x, y) = x $
$ f_(x x) (x, y) = 0 quad f_(y y) (x, y) = 0 $
$ f_(x y) (x, y) = 1 $
であるから、
$ d(X_t Y_t) &= Y_t d X_t + X_t d Y_t\
&quad + 1/2 (0 dot.op d X_t d X_t + 1 d X_t d Y_t + 1 d Y_t d X_t + 0 dot.op d Y_t d Y_t)\
&= Y_t d X_t + X_t d Y_t + d X_t + d Y_t $

5. $f(x) = 1/x$ のとき
$ f^prime (x) = - 1/ x^2 $
$ f^(prime prime) = 2/ x^3 $
であるから、
$ d(1/X_t) = - (d X_t) / X_t^2 + (d X_t d X_t) / X_t^3 $

= SDE : Stochastic Differencial Equation
いま、次のような確率微分方程式 ( SDE ) の解を考える。
$ d X_t = mu (t, X_t) d t + sigma (t, X_t) d W_t quad #text()[( on $PP$ #h(1mm))] $
即ち、
$(Omega, cal(F), PP, (cal(F)_t))$ : フィルトレーション付き確率空間 ( Filtrated Probability Space ) 、\
$W$ : $cal(F)_t$ - BM の下で#footnote[
  このような設定からもわかるように、本当は $d W_t^PP$ と記述するべきである。
]
$ X_t - X_0 = integral_0^t mu (s, X_s) d s + integral_0^t sigma (s, X_s) d W_s $
が成立する $X$ を考える。 

このとき、解には#v(1mm)
-- （弱い）解 : $cal(F)_t$ - 適合な解#v(1mm)
-- （強い）解 : $cal(F)_t^W$ - 適合な解、即ち $W$ が生成する $cal(F)$ に適合な解#v(1mm)
の2種類が存在しており、

以下の Lipschitz 条件を満たすと強い解が一意的に存在することが知られている。#v(1mm)
-- $(t, x)$ に関して $mu, sigma$ : 連続、かつ#v(0.5mm)
$quad exists K : forall t, x, y quad &abs(mu(t, x) - mu(t, y)) <= K abs(x - y)\
&abs(sigma(t, x) - sigma(t, y)) <= K abs(x - y) $

== Black-Scholes 型

$ (d X_t) / X_t = mu_t d t + sigma_t d t $
であって、$X_0 in.small RR$ かつ $mu_t, sigma_t$ : 決定的、とする。

いま、$d(log X_t)$ を考えると
$ d(log X_t) &= (d X_t) / X_t - (d X_t d X_t) / (2 X_t^2)\
&= (mu_t X_t d t + sigma_t X_t d W_t) / X_t - 1/2 (mu_t X_t d t + sigma_t X_t d W_t)^2 / X_t^2\
&= mu_t d t + sigma_t d W_t - 1/2 (mu_t d t + sigma_t d W_t)^2\
&= mu_t d t + sigma_t d W_t - 1/2 (sigma_t^2 d W_t d W_t)\
&= (mu_t - 1/2 sigma_t^2) d t + sigma_t d W_t $
であるから、
$ log X_t - log X_0 = integral_0^t (mu_s - 1/2 sigma_s^2) d s + integral_0^t sigma_s d W_s $
これより、
$ X_t &= e^(log X_0)#h(0.5mm) e^(integral_0^t (mu_s - 1/2 sigma_s^2) d s + integral_0^t sigma_s d W_s)\
&= X_0 #h(0.5mm)e^(integral_0^t (mu_s - 1/2 sigma_s^2) d s + integral_0^t sigma_s d W_s) $

今後、株価のモデリングに使用することを踏まえ、この $X$（幾何ブラウン運動）の性質を簡単に評価する。

-- 平均
$ EE[X_t] &= X_0 EE[exp(underbracket(integral_0^t (mu_s - 1/2 sigma_s^2) d s, "定数") + integral_0^t underbracket(sigma_s, "決定的な関数") d W_s)]\
&quad #text(0.8em)[($because$ 伊藤の等長性から、第二項$tilde.op cal(N)(0, integral_0^t sigma_s^2 d s)$)]\
&= X_0 exp(integral_0^t (mu_s - 1/2 sigma_s^2) d s + 1/2 integral_0^t sigma_s^2 d s) quad #text(0.8em)[($because$ $EE[e^(cal(N)(mu, sigma^2))]=e^(mu + 1/2 sigma^2)$)]\
&= X_0 exp(integral_0^t mu_s d s) $

-- 分散
$ V[X_t] &= EE[X_t^2] - {EE[X]}^2\
&= EE[X_0^2 exp(underline(2 integral_0^t (mu_s - 1/2 sigma_s^2) d s + 2 integral_0^t sigma_s d W_s))]- X_0^2 exp(2integral_0^t mu_s d s)\
&quad #text(0.8em)[($because$ 上と同様に考え、下線部は正規分布)]\
&= X_0^2 exp(2 integral_0^t (mu_s - 1/2 sigma_s^2) d s + 1/2 dot.op 4 integral_0^t sigma_s^2 d s) - X_0^2 exp(2 integral_0^t mu_s d s)\
&= X_0^2 exp(2 integral_0^t mu_s d s){exp(integral_0^t sigma_s^2 d s) - 1} $

とわかる。

特に、パラメータが時間変動しない場合
$ X_t = X_0 e^((mu - sigma^2/2)t + sigma W_t) $
$ EE[X_t] = X_0 e^(mu t) $
$ V[X_t] = X_0 e^(2 mu t )(e^(sigma^2 t) - 1) $
となる。

== Ornstein-Uhlenbeck 型
$ d X_t = kappa_t (mu_t - X_t) d t + sigma_t d t $
であって、$X_0 in.small RR$ かつ $kappa_t, mu_t, sigma_t$ : 決定的、とする。

形態からわかるように、$kappa$ は平均回帰速度 ( mean reversion speed ) である。

いま、この形の $X_t$ を解くために次のような変形を考える。
まず、
$ Y_t = integral_0^t kappa_s d s $
とする。このとき、
$ d Y_t = kappa_t d t $
であるから、
$ d(e^(Y_t)) &= e^(Y_t) (d Y_t + 1/2 d Y_t d Y_t)\
&= e^(Y_t) (kappa_t d t + 0)\
&= e^(integral_0^t kappa_s d s) kappa_t d t $
これより、
$ d(e^(integral_0^t kappa_s d s) X_t) &= e^(integral_0^t kappa_s d s) kappa_t d t X_t + e^(integral_0^t kappa_s d s) d X_t + e^(integral_0^t kappa_s d s) kappa_t d t d X_t\
&= e^(integral_0^t kappa_s d s) {kappa_t d t X_t + kappa_t (mu_t - X_t) d t + sigma_t d W_t + 0}\
&= e^(integral_0^t kappa_s d s) (kappa_t mu_t d t + sigma_t d W_t) $
を得る。これを積分して、
$ e^(integral_0^t kappa_s d s) - 1 dot.op X_0 = integral_0^t kappa_s mu_s e^(integral_0^s kappa_u d u) d s + integral_0^t sigma_s e^(integral_0^s kappa_u d u) d W_s $
整理して、
$ X_t = X_0 e^(-integral_0^t kappa_s d s) + integral_0^t kappa_s mu_s e^(-integral_s^t kappa_u d u) + integral_0^t sigma_s e^(-integral_s^t kappa_u d u) d W_s $
ここで、第二項までは定数、第三項はやはり正規分布となっていることに注意する。


== 1次元線形 SDE
