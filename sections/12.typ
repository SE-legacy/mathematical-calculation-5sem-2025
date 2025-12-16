// NOTE: Лекция 12. 02.12.2025
#set math.equation(numbering: "(1)")
#let numering(n) = $#[(#n)] quad $
#let climits(main, top, bottom) = $limits(main)_(bottom)^(top)$
#let eqcircle = circle(height: 1em, stroke: 0.5pt, [#v(-0.3cm) #align(center + horizon, $eq$)])
#let ltcircle = circle(height: 1em, stroke: 0.5pt, [#v(-0.3cm) #align(center + horizon, $lt$)])
#let iuf = "интегральное уравнение Фредгольма"

== Раздел 4 (Численные методы решения интегральных уравнений)
=== $section$ 1 (решение интегрального уравнения Фредгольма в случае выражденного ядра)

Рассмотрим следующее интегральное уравнение

$
  numering(1) y(x) + lambda dot climits(integral, b, a) A(x, t) y(t) d t = f(x)\
    #[--- #iuf относительно] space y(x) = ? space forall x in [a, b]
$<l12:eq1>

где $lambda$ --- спектральный параметр, $A(x, t)$ --- "ядро", определена и
непрерывна на $[a, b] times [a, b]$ по совокупности переменных $x$ и $t$,
$a$ и $b$ --- известные пределы интегрирования, $f(x)$ --- определенная и
непрерывная на $[a, b]$ функция.

_Подробнее о @l12:eq1 смотри Петровский лекции по теории интегральных уравнений_

Далее будем считать, что #iuf @l12:eq1 на отрезке $[a, b]$ имеет единственное
решение $y(x)$ (другими словами $lambda$ --- отличен от так называемых
характериситческих чисел)

В этом параграфе будем рассматривать #iuf @l12:eq1 с вырожденным ядром, другими
словами, тогда ядерная функция может быть представлена в следующем виде:

$
  numering(2) A(x, t) = climits(sum, n, k = 1) a_k (x) dot b_k (t)
$<l12:eq2>

Таким образом мы имеем следующее уравнение (после подстановки ядра @l12:eq2 в
уравнение @l12:eq1)

$
  y(x) + lambda climits(integral, b, a) (climits(sum, n, k = 1) a_k (x) b_k (t))
    dot y(t) d t = f(x)
$

Применив свойство адитивности определенного интеграла получаем

$
  numering(3) underbrace(y(x), ?) + lambda climits(sum, n, k = 1) (a_k (x)
    dot climits(integral, b, a) underbrace(underbrace(y(t), ?)
    dot b_k, =^#[определим] q_k\, k = overline(1\, n)) d t) = f(x)
$<l12:eq3>

Подвергнем уравнение @l12:eq3 следующим преобразованием

+ Умножим функциональное равенство @l12:eq3 на $b_1 (x)$ и результат проинтегрируем по $(a, b]$;
+ Умножим функциональное равенство @l12:eq3 на $b_2 (x)$ и результат проинтегрируем по $(a, b]$;
$dots$

$n.$ Умножим функциональное равенство @l12:eq3 на $b_n (x)$ и результат проинтегрируем по $(a, b]$;

В результате получим систему следующих скалярных равенств.

$
  numering(4) underbrace(climits(integral, b, a) y(x) b_j (x) d x, = q_j)
    + lambda dot climits(sum, n, k = 1)
        (underbrace(climits(integral, b, a) a_k (x) b_j (x) d x, alpha_(k j))
          dot underbrace(climits(integral, b, a) y(t) b_k (t) d t, q_k)) = \
    = underbrace(climits(integral, b, a) f(x) b_j (x) d x, phi_j),
      space j = overline(1\, n)
$<l12:eq4>

С учетом сделанных обозначений, равенство @l12:eq4 можно переписать в следующем
виде:
$
  numering(4')q_j + lambda dot climits(sum, b, a) alpha_(k j) dot q_k = phi_j, space j
    = overline(1\, n)
$<l12:eq4_shtrix>

По алгебраической природе равенство @l12:eq4_shtrix представляет собо СЛАУ
$n times n$ относительно неу... скаляр. велечин. $q_1, q_2, dots, q_n$
Соответственно перепишем @l12:eq4_shtrix в эквивалентном матричном виде

$
  numering(4'') cases(
  q_1 + lambda (alpha_(1 1) q_1 + alpha_(2 1) q_2 + dots + alpha_(n 1) q_n) = phi_1,
  q_2 + lambda (alpha_(1 2) q_1 + alpha_(2 2) q_2 + dots + alpha_(n 2) q_n) = phi_2,
  dots,
  q_n + lambda (alpha_(1 n) q_1 + alpha_(2 n) q_2 + dots + alpha_(n n) q_n) = phi_n,
  ) <=>\
$<l12:eq4_shtrix_2>
$
  numering(4''') mat(
    (1 + lambda alpha_(1 1)), lambda alpha_(2 1), dots, lambda alpha_(n - 1);
    lambda alpha_(1 2), (1 + lambda alpha_(2 2)), dots, lambda alpha_(n - 2);
    dots, dots, dots, dots,;
    lambda alpha_(n n), lambda alpha_(2 n), dots, (1 + lambda alpha_(n - n));
  ) dot mat(
    q_1; q_2; dots; q_n
  ) = mat(
    phi_1; phi_2; dots; phi_n
  )
$<l12:eq4_shtrix_3>

Решив СЛАУ @l12:eq4_shtrix_3  методом Гаусса (или методом простой итерации, но
он "неточный", хотя сопостовим с методом Гаусса) (метод прогонки не подойдёт)
мы узнаем числовые значения $q_1, q_2, ..., q_n$.

Соответственно обратившись к ранее полученному соотношению @l12:eq3
$
  y(x) + lambda dot climits(sum, n, k = 1) q_k (x) q_k = f (x) =>\
  => y(x) = f(x) - lambda climits(sum, n, k = 1) q_k dot a_k (x)
$<l12:eq5>

Таким образом из вышеизложенного получаем следующий алгоритм решения ...
с вырожденным ядром @l12:eq2
+ по данным #iuf @l12:eq1 и @l12:eq2 строим вспомогательную слау @l12:eq4_shtrix_3
+ строим  СЛАУ @l12:eq4_shtrix_3 $--> q_1, dots q_n$
+ Получаем решение #iuf @l12:eq1 и @l12:eq2 по явной аналитической формуле @l12:eq5
