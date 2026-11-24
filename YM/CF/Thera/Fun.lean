import YM.CF.Thera.Rider
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Spire
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
-- spatial reflection, finite. gauge separate.
variable {n m:Type*}[LinearOrder n][Fintype n]{b c:Bool}(U:UNI n)(r:Bool)
def jazz(v:Op n):=if r then -star v else v
lemma spice(B W C K:Op n)(t:IsUnit (1+bentT K B W C)) : let f:=sings b U; traitP (f B) (f K) (f W) (f C)= f (traitP B K W C):=by
 intro f; unfold traitP laneP creep bentT; unfold f; simp only [singT,win_m,win_l,win_a,win_i,map_mul,map_add,map_sub,map_one]; rw [show twist U (windX b (1+ K*(B*W)*C)⁻¹)= (sings b U (1+K*(B*W)*C))⁻¹ from singsUnit b U _ t]; simp only [singT,win_m,win_a, win_i,map_one,map_mul,map_add]
lemma icing[Nonempty n](B K W C:Op n)(h:‖bentT K B W C‖<1): let f:=sings b U; invoice (bentT (f K) (f B) (f W) (f C))= cSignX b (invoice (bentT K B W C)):=by
 intro f; have ht:bentT (f K) (f B) (f W) (f C)=f (bentT K B W C):=by unfold f bentT; simp only [singT,win_m,map_mul]
 rw [ht, show f _=_ from singT b U (bentT K B W C),bill_invariant _ _ _,awards _ h]; cases b; exact h; change ‖cc _‖<_; rw [norm_cc]; exact h
lemma frame_turn(B W K C:Op n)(X P V E T L:Op n)(h:Clad B W K C X)(g:Clad P V E T L)(b:Bool)(hc:sings b U B=P)(hv:sings b U W=V)(he:sings b U K=E):sings b U X=L:=by
 let F:=sings b U
 have hz:F X*throat P V E=P:=by rw [throat,←he,←hv,←hc]; unfold F; rw [←singm,←singm,←singm,h.left] -- tune nested
 have hp:F X * V=F X:=by rw [←hv,←singm,h.stem]
 change F X=L; rw [←hp, show V=throat P V E*L from g.right.symm, ←mul_assoc, hz,g.tray]
section lat
variable {N Q A L B:Side} (G:Ratio N Q)(h:G.count=L)
lemma spry(X:Op (Iota G)) : endorse G (summit (patchQ G) X)=hood G*X*hood G:=by
 rw [←edgeDesk,lighthouse]; apply op_columns; intro i; rw [act_mul,act_mul, economy, summit_rule]; simp only [←stance, trails]
lemma endorseI: Injective (endorse G):=by intro B V h; simp only [←edgeDesk] at h; ext i j; rw [←desk_at (patchQ G) B,h,desk_at]
lemma everyK(k:Bool)(T:Op (Iota G)) (a:Shape)(t:ColorT k)(U:UNI SpinIdx): summit (patchQ G) (sings k (pflux a G U t) T)= sings k (prepU a U t N) (summit (patchQ G) T):=by
 apply endorseI G; rw [←clampS,spry,spry]; simp_rw [singm,hoodL]
end lat
end YM.CF.Thera
