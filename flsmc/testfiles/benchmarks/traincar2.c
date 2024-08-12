
/*@
  \flsmc::distribution s0, "Uniform", 0.0, 4.6;
	\flsmc::distribution s1, "Uniform", 0.0, 10.0;
	\flsmc::distribution s2, "Uniform", 0.0, 10.0;
  \flsmc::prob_ensures 0.99, 0.001,
	\flteq(\result, (-3.795323e2) * s0 + (-5.443608e2) * s1 + 92.729 *
		s2 + 4.5165916241610748e3, 0.00176);
*/
float traincar1(float s0, float s1, float s2) {
    // require(0 <= s0 && s0 <= 4.6 &&
			// 			 0 <= s1 && s1 <= 10 &&
			// 			 0 <= s2 && s2 <= 10)
    return (-3.795323e2) * s0 + (-5.443608e2) * s1 + 92.729 *
			s2 + 4.5165916241610748e3;
}
todo:fix traincar2-3-4
