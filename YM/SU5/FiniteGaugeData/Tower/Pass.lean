import YM.SU5.FiniteGaugeData.Tower.Score
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# The actual separated algebra & reflection laws through period transport

All eventual-in-period-only conditions are on the same Y (H); still need to
pay legalAt(kick from *that* n, s<*that* UV). Terminal Λ.x remains fixed.
Overlap of boxes does not change the limiting flow of a given argument.
-/
section operate
variable (n k₀:ℕ→ℕ)(D:Cresc Y H n k₀)
variable {S U:Finset Cover}{F G:Family (tent Y H)}
local notation "W"=>wingspan Λ l
local notation "T" S:max F:max=>destined Y H s n k₀ S D F
local notation "b" i:max S:max F:max=>block Y H s (n i) (k₀ i) S F
variable (x : InTest (tent Y H) true S false F)
variable (v:Tendsto n atTop atTop)(w:∀s,∀ᶠ r in atTop, legalAt Y s (n r) (k₀ r))
lemma turning (A:Finset Cover): ∀ᶠ i:ℕ in atTop, Tivoli A ((K).c (momentm Y i s)):= ((momentum Y s).eventually (separates K (tips A))).mono fun _ h=> ⟨⟨h⟩⟩
include D v x w
lemma cross_compatible (a:S⊆U): T S F=T U F:=by
 funext m z
 apply tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D S x m z) (ev_image Y H s n k₀ D U (x.mono a) m z)
 filter_upwards [v.eventually (turning Y H (s+1) (W U)),w s] with r t h
 change (b r S F) m z=(b r U F) m z
 rw [upper_overlap Y H s S _ _ h x a t]

omit x v w in
lemma add_one {S: Finset Cover}{f g}(x:InTest K true S false f)(u:InTest K true S false g): T S (f+g)=(T S f)+(T S g):=by
 funext m z
 exact tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D S (x.add u) m z) ((ev_image Y H s n k₀ D S x m z).add (ev_image Y H s n k₀ D S u m z)) (Eventually.of_forall fun r=>congrFun (congrFun (add_scheme Y H s _ _ x u) m) z)
omit v w in
lemma scales_one (a:ℂ): T S (a • F) =a • (T S F):=by
 funext m z
 exact tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D S (InTest.smul a x) m z) ((ev_image Y H s n k₀ D S x m z).const_smul a) (Eventually.of_forall fun r=>congrFun (congrFun (scale_scheme Y H s _ _ x a) m) z)

omit x
lemma unidad (S:Finset Cover):T S 1=1:=by
 funext m z; apply tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D S InTest.one m z) (tendsto_const_nhds (f:=atTop) (x:=(1:Family (tent Y H)) m z))
 filter_upwards [w s,v.eventually (turning Y H (s+1) (W S))] with r u h
 exact congrFun (congrFun (block_unit Y H s _ _ u h) m) z

variable (a:Axis)(e:ℤ)
local notation "S'"=> reflectedBox a e S
local notation "z₀"=> (Λ.R.L.val*e:ℤ)
local notation "Z₀" R:max=>mirror (tent Y H) a (z₀) R
include x
omit D w v
lemma christmas : ∀ᶠ i in atTop,∀ k, legalAt Y s i k→
 block Y H s i k (S') (mirror (tent Y H) a e F)= Z₀ (block Y H s i k S F):=by
 let V₁:=reflectedBox a z₀ (W S)
 let V₂:= W (reflectedBox a e S)
 filter_upwards [turning Y H (s+1) (W S),turning Y H (s+1) V₂, turning Y H (s+1) (V₁∪ V₂)] with i hx hy hp k m
 let g':= block Y H s i k S F
 have he:= axial (tent Y H) a e x
 have ht:= booked Y H s i k S F; have hu:= axial (tent Y H) a z₀ ht
 apply stationary_ext Y H (s+1) (V₁∪ V₂) i hp.hosp ((booked Y H s i k (S') (mirror (tent Y H) a e F)).mono subset_union_right) (hu.mono subset_union_left)
 rw [(distribute_arith Y H (s+1) i g' g' 0).2.2.2.2,reserved Y H s S i k m x hx,reserved Y H s _ i k m he hy]
 unfold aboveD; rw [(distribute_arith Y H s i F F 0).2.2.2.2]; unfold nextMark
 let Z:=((Y.voyage i).X (Y.uv k)).gram; let A:= ((Y.voyage i).X (Y.uv k)).wave; let K₁:= steps Λ.V (Y.ir i) Λ.block (Y.uv k); let V:= (Y.voyage i).CapeT; let g:= (Vale.apt (Y.ir i) Λ.block Λ.R.L s); let p:= (fullness Y i k m.1).cap_grant
 obtain ⟨t⟩:= p.grant s m.2; obtain ⟨y,u,v,F0,s'⟩:=t.cap
 exact rising g (K₁ s) Λ.K.j ((A s).val) (Z (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Z (s+1)).beta (V s) a e (p.aligned s m.2) (stationed Y H s S i x) (p.branch s m.2) F0 (show Stencil.LaurentRadius _ Λ.R.L (aliasLaw Λ) from Journey.legal Λ) t.legal.1 t.legal.2
include D w v
lemma both_bands:T (S') (mirror K a e F) = Z₀ (T S F):=by
 funext m z
 have ht:= Fock.theta_cont (carR a z₀ ((K).c m)) -- notation
 apply tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D (S') (axial K a e x) m z) (ht.continuousAt.tendsto.comp (ev_image Y H s n k₀ D S x m (reflFields a z₀ z)))
 filter_upwards [v.eventually (christmas Y H s x a e),w s] with r j b'
 exact congrFun (congrFun (j (k₀ r) b') m) z

local notation "C₀"=> (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l))
variable (y:InTest (tent Y H) true U false G)(C:separated (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)) S U)
omit v w D
include x y C
set_option maxHeartbeats 700000 in
lemma chorus : ∀ᶠ i in atTop, ∀ k,legalAt Y s i k→
 block Y H s i k (S∪U) (F*G)=block Y H s i k S F*block Y H s i k U G:=by
 let T':= W (S∪U); have h₁:W S⊆ T':=wingspan_mono subset_union_left; have h₂:W U⊆ T':=wingspan_mono subset_union_right
 filter_upwards [turning Y H (s+1) T',turning Y H (s+1) (W S),turning Y H (s+1) (W U),(momentum Y s).eventually (wrapped_far (tent Y H) C₀ S U C)] with i P₀ h t V k u
 let J:=block Y H s i k S F; let Z:= block Y H s i k U G
 have hp:= booked Y H s i k S F; have ht:= booked Y H s i k U G
 apply stationary_ext Y H (s+1) T' i P₀.hosp (booked ..) (.mul (hp.mono h₁) (ht.mono h₂))
 rw [(distribute_arith Y H (s+1) i J Z 0).2.1,reserved Y H s S _ _ u x h,reserved Y H s U i k u y t,reserved Y H s (S∪U) i k u (show InTest (tent Y H) true (S∪U) false _ from (x.mono subset_union_left).mul (y.mono subset_union_right)) P₀]
 change ∀ a∈Satin.region S ((tent Y H).c (momentm Y i s)), ∀ b'∈Satin.region U ((tent Y H).c (momentm Y i s)), C₀ < separation a b' at V
 rw [terrain Y H (Y.ir i) s] at V
 unfold aboveD; rw [(distribute_arith Y H s i F G 0).2.1]; unfold nextMark
 let Q:=((Y.voyage i).X (Y.uv k)).gram; let A:= ((Y.voyage i).X (Y.uv k)).wave; let K₁:= steps Λ.V (Y.ir i) Λ.block (Y.uv k); let Y':= (Y.voyage i).CapeT; let g:= (Vale.apt (Y.ir i) Λ.block Λ.R.L s); let p:= (fullness Y i k u.1).cap_grant
 obtain ⟨t'⟩:= p.grant s u.2; obtain ⟨u',v,aX,F0,j⟩:= t'.cap
 exact separated_mult g (K₁ s) Λ.K.j ((A s).val) (Q (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Q (s+1)).beta (Y' s) (R:=aliasLaw Λ) (show Stencil.LaurentRadius _ Λ.R.L _ from Journey.legal Λ) F0.bill (p.branch s u.2) t'.legal.1 t'.legal.2 _ _ (stationed Y H s S i x) (stationed Y H s U i y) (tissue Y i s) V
include D w v
lemma parted: T (S∪U) (F*G)= (T S F)*(T U G):=by
 funext m z
 apply tendsto_nhds_unique_of_eventuallyEq (ev_image Y H s n k₀ D (S∪U) (show InTest (tent Y H) true (S∪U) false _ from (x.mono subset_union_left).mul (y.mono subset_union_right)) m z) ((ev_image Y H s n k₀ D S x m z).mul (ev_image Y H s n k₀ D U y m z))
 filter_upwards [v.eventually (chorus Y H s x y C),w s] with r j t
 exact congrFun (congrFun (j (k₀ r) t) m) z
end operate
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.parted
#print axioms YM.CF.Buffered.Afterglow.Tower.both_bands
