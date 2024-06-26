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

= 確率積分

$H$ : 連続適合#footnote[
  #definition[
    $X_t$ : $F_t$ - 適合であるとは、
    $ forall t quad X_t : cal(F)_t "- 可測" $
  ]
  即ち、その時点までの情報で決まっていることを意味している
]過程、$W$ : $cal(F)_t$ によって生成されたBM ( Brownian Motion ) であるとする。

いま、
$ integral_0^t H_s d W_s $
なる確率変数を定めたい。
あるいは、
$ (integral_0^t H_s d W_s)_(t >= 0) $
なる確率過程を定めたい。

改めて前提を整理すると、
$ integral_0^t H_s d W_s $
において考えているのは、$omega in.small Omega$ をひとつ fix したとき、ある時刻 $s$ を与えると#v(1mm)
-- $s arrow.r.bar H_s (omega)$ : 普通の関数（Path）#v(1mm)
-- $s arrow.r.bar W_s (omega)$ : 普通の関数（Path）#v(1mm)
であるように、それぞれはこれまでに定義してきた（見知った）関数である。

一方で、上の確率変数を Lebersgue - Stieltjes 積分（$arrow.l.r.double$ Path $omega$ ごとの積分）として定めるのは無理であることが知られている。即ち、
$ sum_(i=1)^n H_(t_i) (omega) (W_(t_(i+1)) (omega) - W_(t_i) (omega)) $
を考えられないということである。

これは、$W_t$ が2次変分を持つことから、有界変動#footnote[
  ブラウン運動が無限にギザギザしているという性質は、積分において都合が悪いということである。
]な Path を確率 $1$ で持たないことによる。

そこで、Lebersgue 積分のように各点収束を考えるのではなく、分割における左側の関数値を代表点として $L^2$ 収束#footnote[
  これより、確率収束していることが言える ($because$ #h(1mm) No.5) *ここら辺ブラウン運動の回を見直して直しておく*
]を考えればよい、というのが確率積分（伊藤積分）の骨子である。

これより、積分の構成や証明などで高度な部分は割愛しつつ、満たしてほしい性質から天下り的に確率積分を考える。

例によって、$Delta$ : $0=t_0 < dots.c < t=t_n$ を $[0, t]$ の分割とする。
このとき、
$ A_t^Delta := sum_(i=1)^n H_(t_(i-1)) (W_(t_i) - W_(t_(i-1))) $
$ B_t^Delta := sum_(i=1)^n H_(t_i) (W_(t_i) - W_(t_(i-1))) $
なる確率変数を考える。それぞれ、各分割地点における左（右）側を代表点とした確率積分の近似である。
$ B_t^Delta - A_t^Delta = sum_(i=1)^n ( H_(t_i) - H_(t_(i-1)) ) (W_(t_i) - W_(t_(i-1))) $
であるから、例えば $H=W$ の場合を考えると、
$ B_t^Delta - A_t^Delta &= sum_(i=1)^n (W_(t_i) - W_(t_(i-1)))^2\
&attach(arrow.r, t:abs(Delta) arrow.r 0) t #h(3mm) (eq.not 0) $
つまり $B_t^Delta eq.not A_t^Delta$ である。

また、
$ B_t^Delta + A_t^Delta &= sum_(i=1)^n (W_(t_i)) + W_(t_(i-1)) (W_(t_i)) - W_(t_(i-1))\
&= sum_(i=1)^n (W_(t_i)^2 - W_(t(i-1))^2)\
&= W_t^2 - 0\
&= W_t^2 $

よって
$ A_t^Delta tilde.eq 1 / 2 (W_t^2 - t) $
$ B_t^Delta tilde.eq 1 / 2 (W_t^2 + t) $
と考えられる。特に、上の $A_t^Delta$ の右辺はマルチンゲールであり、性質がよさそうである。

これを念頭に、左側を代表点とするものを確率積分であると考えると、今後の見通しがよさそうである。

例えば、
$ Delta : (0=t_0 < dots.c < s=t_k < dots.c < t=t_n) $
として、$[0, t]$ の $s$ を通る分割を以下では考える。
このとき、
$ EE[A_t^Delta|cal(F)_s] &= EE[sum_(i=1)^n H_(t_(i-1)) (W_(t_i) - W_(t_(i-1)))|cal(F)_(t_k)]\
&= sum_(i=1)^k H_(t_(i-1)) (W_(t_i) - W_(t_(t_(i-1))))\ 
&+ sum_(i=k+1)^n EE[EE[H_(t_(i-1)) (W_(t_i) - W_(t_(t_(i-1))))|cal(F)_(t_(i-1))]|cal(F)_(t_k)]\
& #text(0.8em)[($because$ $cal(F)_(t_k)$ - 可測性と Tower Law)]\
&= A_s^Delta + sum_(i=k+1)^n EE[H_(t_(i-1)) EE[W_(t_i) - W_(t_(i-1))|cal(F)_(t_(i-1))]|cal(F)_(t_i)]\
&= A_s^Delta #text(0.8em)[($because$ $W$ はマルチンゲールだから増分は $0$)] $

よって、$integral_0^t H_s d W_s$ は、$t$ についてマルチンゲールになるべき量である

加えて、天下り的ではあるが、$H$ : 有界として
$ EE[(A_t^Delta)^2] &= EE[ sum_(i=1)^n sum_(j=1)^n H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1)))]\
&= sum_(i=1)^n EE[H_(t_(i-1))^2 (W_(t_i) - W_(t_(i-1)))^2] \
&+ 2 sum_(i > j) EE[H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1))] $
であるから、Tower Law により
$ ("第一項の中身") &= EE[EE[H_(t_(i-1))^2 (W_(t_i) - W_(t_(i-1)))^2|cal(F)_(t_(i-1))]]\
&= EE[H_(t_(i-1))^2 EE[(W_(t_i) - W_(t_(i-1)))^2|cal(F)_(t_(i-1))]]\
&= EE[H_(t_(i-1))^2 (t_i - t_(i-1))] quad #text(0.8em)[($because$ 分散)] $
$ ("第二項の中身") &= EE[EE[H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1)))|cal(F)_(t_(i-1))]]\
&= EE[H_(t_(i-1)) H_(t_(j-1)) (W_(t_j) - W_(t_(j-1))) EE[(W_(t_i) - W_(t_(i-1)))|cal(F)_(t_(i-1))]] quad #text(0.8em)[($because$ 独立増分性)]\
&= 0 $
より、
$ EE[(A_t^Delta)^2] &= EE[sum_(i=1)^n H_(t_(i-1))^2 (t_i - t_(i-1))]\
&attach(arrow.r, t:abs(Delta) arrow.r 0) EE[integral_0^t H_s^2 d s] $
である。
これより、冒頭で正体がつかめなかった『確率積分』の2乗の期待値は、（適合過程として）知っている関数の2乗の期待値に収束していることがわかる。

これまでの結果をまとめると、
$integral_0^t H_s d W_s$ は、次の伊藤の等長性という式を満たすべきである。
$ EE[(integral_0^t H_s d W_s)^2] = EE[integral_0^t H_s^2 d s] $
このとき、確率積分 $integral_0^t H_s d W_s := I$ は $L^2$ 可積分でマルチンゲールであり、
$ bar.v.double I bar.v.double_(L^2 (Omega, PP))^2 = bar.v.double H bar.v.double_(L^2 (Omega times [0, t], cal(P), PP times lambda))^2 $
と言える#footnote[
  右辺の $PP$ は確率測度で $lambda$ はルベーグ測度、また $cal(P)$ はこの積分を成立させるための（舞台設定としての）加法族である。
]。

これより、この $I$ の2次変分を考えたい#footnote[証明なしで以下を考えることになるが、確率積分 $integral_0^t H_s d W_s$ が連続であると都合がよい]。$I = integral_0^t H_s^2 d s$ において、#v(1mm)
-- $H_s (omega)$ : $omega$ を与えるごとに生成される連続な Path #v(1mm)
-- $d s$ は普通の Lebersgue 積分#v(1mm)
であるから、$omega$ を与えるごとに値が確定する積分であることに注意する。\
*2次変分の性質（ちゃんとしたやつ）のっける*\
-- $0$ スタート
-- 増加
-- 連続なパスを持つ
-- $A^2 - X$ がマルチンゲール
このとき、上の3つは直観的に成立を期待できる。そこで、
$ Delta : (0=t_0 < dots.c < s=t_k < dots.c < t=t_n) $
として、
$ X_t^Delta := sum_(i=1)^n H_(t_(i-1))^2 (t_i - t_(i-1)) $
$ X_s^Delta := sum_(i=1)^k H_(t_(i-1))^2 (t_i - t_(i-1)) $
とおくと、
$ EE[(A_t^Delta)^2 - X_t^Delta|cal(F)_s] &= EE[sum_(i=1)^n sum_(j=1)^n H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1))) \
&quad - sum_(i=1)^n H_(t_(i-1))^2 (t_i - t_(i-1)) |cal(F)_s]\
&= sum_(i=1)^n EE[H_(t_(i-1))^2 ((W_(t_i) - W_(t_(i-1)))^2 - (t_i - t_(i-1)))|cal(F)_(t_k)]\
&quad + 2 sum_(i>j) EE[H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1)))|cal(F)_(t_k)] $
であるから、

第一項の各項は#v(1mm)
-- $i <= k$ のとき
$ = H_(t_(i-1))^2 ((W_(t_i) - W_(t_(i-1)))^2 - (t_i - t_(i-1))) $
として可測性より外に出せる#v(1mm)
-- $i > k$ のとき
$ &= EE[EE[H_(t_(i-1))^2 ((W_(t_i) - W_(t_(i-1)))^2 - (t_i - t_(i-1)))|cal(F)_(t_(i-1))]|cal(F)_(t_k)]\
&= EE[H_(t_(i-1))^2 EE[(W_(t_i) - W_(t_(i-1)))^2|cal(F)_(t_(i-1))]]\
&quad - EE[H_(t_(i-1))^2 (t_i - t_(i-1))|cal(F)_(t_k)] quad #text(0.8em)[($because$ $t_i - t_(i-1)$ は定数)]\
&= EE[H_(t_(i-1))^2(t_i - t_(i-1))|cal(F)_(t_k)] - EE[H_(t_(i-1))^2(t_i - t_(i-1))|cal(F)_(t_k)] quad &#text(0.8em)[($because$ 独立増分性)]\
&= 0 $
また、第二項の各項は $i > k$ のとき
$ &= EE[EE[H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1)))|cal(F)_(t_(i-1))]|cal(F)_(t_k)]\
&= EE[H_(t_(i-1)) H_(t_(j-1))  (W_(t_j) - W_(t_(j-1))) EE[(W_(t_i) - W_(t_(i-1)))|cal(F)_(t_(i-1))]|cal(F)_(t_k)]\
&= 0 quad #text(0.8em)[($because$ 独立増分性)] $
であるから、
$ EE[(A_t^Delta)^2 - X_t^Delta|cal(F)_s] &= sum_(i=1)^k H_(t_(i-1))^2 (W_(t_i) - W_(t_(i-1)))^2 - sum_(i=1)^k H_(t_(i-1))^2 (t_i - t_(i-1))\
&quad + 2 sum_(k>=i>j) H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1))) \
&= (A_s^Delta)^2 - X_s^Delta $
となり、所望の結果を得る#footnote[
  ここで、$(A_s^Delta)^2$への変形には一般形 $H_(t_(i-1)) H_(t_(j-1)) (W_(t_i) - W_(t_(i-1))) (W_(t_j) - W_(t_(j-1)))$ の対角線領域と三角形領域の和が $k times k$ の正方形となることを用いた。
]。

