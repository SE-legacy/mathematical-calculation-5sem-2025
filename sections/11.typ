// NOTE: Лекция 11. 25.11.2025
#set math.equation(numbering: "(1)")
#let eqcircle = circle(height: 1em, stroke: 0.5pt, [#v(-0.3cm) #align(center + horizon, $eq$)])
#let ltcircle = circle(height: 1em, stroke: 0.5pt, [#v(-0.3cm) #align(center + horizon, $lt$)])
#let ody = "обыкновенному дифферинцеальному уравнению"
#let ky = "краевому условию"
#let mnk ="метода неопределенных коэффициентов"
#let kz = "краевой задачи"
#let numering(n) = $#[(#n)] quad $
#let climits(main, top, bottom) = $limits(main)_(bottom)^(top)$

== Параграф 3 (раздел 3) (Метод неопределенных коэффициентов в решении краевой задачи для оду $I I$ порядка)
Попреженему решаем следующую краевую задачу

$
  numering(1) y'' + p(x) y' + q(x) y = f(x)
    space #[--- оду 2 порядка неизв. функции]\
    space y = y(x) #[--- ?] space forall x in (0, T)
$<l11:eq1>
$
	numering(2) y(0) = y(T) = 0 space #[--- краев услов.]
$<l11:eq2>


$
	cases(
		y'' + p(x) y' + g(x) y = f(x),
		y(0) = y(T) = 0
	)
$

Идея метода неопределенных #mnk решения #kz заключена в поиске
неизвестной функции $y(x)$, являющейся решением #kz в следующем виде:

$
  y(x) = limits(sum)^n_(k = 1) underbrace(a_k, ?\ #[неопрделенные\ коэффициенты]) phi_k (x)\
$<l11:eq3>

где $phi_k (x), k = overline(1\, n)$ --- являются конечным набором в системе
_линейно-независимых функций_ ${phi_k (x)}_(k = 1)^infinity$. $y(x)$ должна
иметь производные непрерывные на $x$

+ Покажем, что для того, чтобы искомое представление @l11:eq3 давало дважнынерпрывную
  на отрезке $[0, T]$ функцию необходимо, чтобы функции $phi_k (x), k =
  overline(1\, n)$ также были дважды непрерывно дифференицруемы на отрезке
  $[0, T]$. Другими словами, если $phi_k (x), k = overline(1\, n) in C^2 [0, T]
  => y(x) in C^2 [0, T]$ по @l11:eq3
  $
     numering(4) phi_k (x), k = overline(1\, n) in C^2 [0, T]
  $<l11:eq4>
  $
    cases(reverse: #true,
      y(x) =^#[@l11:eq3] limits(sum)^n_(k = 1) a_k underbrace(phi_k (x)
        , limits(in C[0, T])_#[непрерывн]) in C [0, T],
      y'(x) =^#[@l11:eq3] limits(sum)_(k = 1)^n a_k underbrace(phi'_k (x)
        , limits(in C[0, T])_#[непрерывн]) in C [0, T],
      y''(x) =^#[@l11:eq3] limits(sum)_(k = 1)^n a_k underbrace(phi''_k (x)
        , limits(in C[0, T])_#[непрерывн]) in C [0, T]
    ) y(x) in C^2 [0, T]
  $
// FIX: Рисунок 2
+ Покажем, что для того, чтобы искомое представление @l11:eq3 удовлетворяло
  краевым условиям @l11:eq2 необходимо, чтобы $phi_k (x), k = 1, dots, n$
  удовлетворяли #ky @l11:eq2. Другими словами
  $
    numering(5) phi_k (x), k = overline(1\, n) space : space phi_k (0) = phi_k (T) = 0,\
      forall k = overline(1\, n)
  $<l11:eq5>

  $
    cases(
      y(0) =^#[@l11:eq3] limits(sum)_(k = 1)^n a_k dot underbrace(phi_k (x)
        , #[Если] = 0) =^#[@l11:eq5] 0,
      y(T) =^#[@l11:eq3] limits(sum)_(k = 1)^n a_k dot underbrace(phi_k (T)
        , #[Если] = 0) =^#[@l11:eq5] 0
    )
  $
+ С целью найти (неизвестные) неопределенные коэффициенты @l11:eq3 подставим
  данное представление #ody @l11:eq1. В результате такой подстановки получаем
  $
    numering(6) limits(sum)^n_(k = 1) underbrace(a_k, ?) phi''_k (x)
      + p(x) limits(sum)_(k = 1)^n underbrace(a_k, ?) phi'_k (x)
      + q(x) limits(sum)_(k = 1)^n underbrace(a_k, ?) phi_k (x)
      = f(x)
  $<l11:eq6>

  Приведем подобные слагаемые в левой части функционального равенства
  $
    numering(6') limits(sum)_(k = 1)^n a_k dot
      underbrace([ phi''_k (x) + p(x) dot phi'_k (x) + q(x) phi_k (x) ], #[... функции])
      = underbrace(f(x), #[функция])
  $<l11:eq6_shtrix>

  С тем чтобы "разможножить" функциональное уравнение @l11:eq6_shtrix до системы
  скалярных уравнений введем на отрезке $[0, T]$ следующий набор узлов;
  $
    [0, T]: space 0 < x_1 < x_2 < dots < x_n ltcircle T, space x_(k + 1) - x_k = h
  $
  И спроецируем уравнение @l11:eq6_shtrix на введенные узлы

  $
    numering(7) limits(sum)_(k = 1)^n a_k
      dot [ phi''_k (x_j) + p(x_j) dot phi'_k (x_j) + q(x_j) phi_k (x_j) ]
      = f(x_j), space j = overline(1\, n)
  $<l11:eq7>


По своей алгебраической природе числовые равенства @l11:eq7 представляют собой
СЛАУ размерности $n times n$ относительно искомых коэффициентов $a_1, a_2, dots,
a_n$

Соответственно решив вспомогательную систему @l11:eq7 (методом Гаусса, методом
простой итерации, методом прогонки здесь не подходит) мы сможем найти искомые
коэффициенты $a_1, a_2, dots, a_n$

Соответственно, найдя коэффициент $a_1, a_2, dots, a_n$ и подставив их в искомое
представление @l11:eq3 мы получим явную аналитическую формулу искомого решения
#kz @l11:eq1 @l11:eq2
$
  numering(8) y(x) approx climits(sum, n, k = 1) a_k dot phi_k (x)
$<l11:eq8>
