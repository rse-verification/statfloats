/*@
  \flsmc::distribution atts0, "Uniform", 3.0, 9.0;
  \flsmc::distribution atts1, "Uniform", 1.5, 5.0;
  \flsmc::distribution atts2, "Uniform", -2.0, 10.0;
  \flsmc::distribution atts3, "Uniform", -1.0, 3.5;
  \flsmc::prob_ensures 0.99, 0.001,
  \flteq(\result, ((0.052100253064028955) * atts0 + (-0.8942341911807864) * atts1
    + (0.40478255170032273) * atts2 + (-0.93774690197704236) * atts3) -
    ((-0.85073072819636686) * atts0 + (-0.98664016916368502) * atts1 +
      (1.3809517485817782) * atts2 + (1.8653450939330991) * atts3),
          0.00000523);
*/
float classIDX2 (float atts0, float atts1, float atts2, float atts3) {
    // require(3.0 <= atts0 && atts0 <= 9.0 &&
    //         1.5 <= atts1 && atts1 <= 5.0 &&
    //         -2 <= atts2 && atts2 <= 10 &&
    //         -1.0 <= atts3 && atts3 <= 3.5)
    return ((0.052100253064028955) * atts0 + (-0.8942341911807864) * atts1
      + (0.40478255170032273) * atts2 + (-0.93774690197704236) * atts3) -
      ((-0.85073072819636686) * atts0 + (-0.98664016916368502) * atts1 +
        (1.3809517485817782) * atts2 + (1.8653450939330991) * atts3);
}
