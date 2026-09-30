/*@
  \flostat::distribution atts0, "Uniform", 3.0, 9.0;
  \flostat::distribution atts1, "Uniform", 1.5, 5.0;
  \flostat::distribution atts2, "Uniform", -2.0, 10.0;
  \flostat::distribution atts3, "Uniform", -1.0, 3.5;
  \flostat::prob_ensures 0.99, 0.001,
  \flteq(\result, ((-0.85073072819636686) * atts0 + (-0.98664016916368502) * atts1 +
            (1.3809517485817782) * atts2 + (1.8653450939330991) * atts3)
            - ((0.18424469636214999) * atts0 + (0.45123431334216657) *
              atts1 + (-0.80794264540764449) * atts2
              + (-0.45071126534400952) * atts3),
          0.00000693);
*/
float classIDX0 (float atts0, float atts1, float atts2, float atts3) {
    // require(3.0 <= atts0 && atts0 <= 9.0 &&
    //         1.5 <= atts1 && atts1 <= 5.0 &&
    //         -2 <= atts2 && atts2 <= 10 &&
    //         -1.0 <= atts3 && atts3 <= 3.5)
    return ((-0.85073072819636686f) * atts0 + (-0.98664016916368502f) * atts1 +
              (1.3809517485817782f) * atts2 + (1.8653450939330991f) * atts3)
              - ((0.18424469636214999f) * atts0 + (0.45123431334216657f) *
                atts1 + (-0.80794264540764449f) * atts2
                + (-0.45071126534400952f) * atts3);
}
