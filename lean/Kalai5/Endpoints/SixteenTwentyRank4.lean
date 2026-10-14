import Kalai5.Endpoints.SixteenTwenty
import Kalai5.A16.Main20

/-!
# Rank four at `(16,20)`

`A16Mid20` from the A16 certificate at twenty facets (`IsCSPolytope5.a16_20`): trees with target
twenty-one polar vertices, and count leaves (`242` distinct tight sets of certified facets, hence
`242` proper faces) where twenty facets really occur.
-/

namespace Kalai5

/-- **Rank four with four to six full pairs at `(16,20)`.** -/
theorem a16Mid20_proof : A16Mid20 := fun _ hP hv hh _ _ hu hfull => hP.a16_20 hv hu hfull hh.le

end Kalai5
