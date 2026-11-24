import YM.SU5.Reconstruction.Quanta.NorthTapes
import YM.SU5.Reconstruction.Oblique.Consulting

/-! # Minus one is a true Spin symmetry, odd letters all on original sharp! -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.QuantaCore
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K₁"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)

open PhaseChoice Tapestry Tapestry.Altitude Spark
-- the CENTRAL Spin element
noncomputable def once : UNI SpinIdx:= Fock.phaseU (-1) (by simp)
lemma once_jet: JetS 1 false false QuantaCore.once:=by
 refine ⟨fun a=>?_,?_,?_⟩
 · change twist once (gammaOp a)=_; unfold once; rw [rankPhase]; rfl
 · change twist once grading= _; unfold once; rw [rankPhase]; rfl
 change (((-1:ℂ) • (1:Op SpinIdx))*spinJ)= spinJ * cc ((-1:ℂ) • (1:Op SpinIdx)); simp
lemma bought_once (N:Side): prepU (incX 1) once inert N = phaseU (-1) (by simp):=by
 apply Subtype.ext; change _= (-1:ℂ) • _
 rw [← (show (prepU (incX 1) 1 inert N).val=1 from congrArg Subtype.val (prep_one N))]
 exact Nacre.Ygs _ once 1 (by rfl) -- tune
section tranche
variable (i' k':ℕ)
local notation "M"=> Y.uv k'
local notation "Yc"=> Y.voyage i'
local notation "L₁" s:max=>side Y i' s
local notation "ν"=>side Y i' M
local notation "X" s:max => ((Y.voyage i').X (Y.uv k')).gram s
local notation "T"=>Y.meter.a M
local notation "YT" s:max=> (Y.voyage i').CapeT s
local notation "PU"=> Λ.U
local notation "Zn"=>capP (K:=Λ.K) PU ((X M).beta) (T) (m:=mesh (Y.ir i') Λ.R.L M)

lemma steel_grade (x:Orbit (side Y i' (Y.uv k'))){B:Finset (Single (side Y i' (Y.uv k')))}{f:FC (Single (side Y i' (Y.uv k')))}(h:Sector B true f): letterRead f (denZ (X M) Λ.U (YT M) x)=0:=by
 let A:=incX (1:Signed); let W:= denZ (X M) Λ.U (YT M) x; let U:=prepU A once (xtra false) ν
 change inner ℂ (Dial.mateK ν) (acts f W)=_
 let t:JetS A.s false false once:=once_jet; let U₀:=Spire.arum U false false (Dial.mateK ν)
 have hx:W=U₀ W:=by
    unfold W U₀; rw [Y.whole]; have hx:= tenor Y i' k' x.1 A once t; rw [show stir (xtra false) A x.1=x.1 from Nacre.blank _] at hx; exact hx.symm -- ν expected N
 have hp:Spire.tourP U false false f= -f:=by change twist (quantU (prepU (incX 1) once inert ν)) f=_; rw [bought_once]; simpa using h.grade_diag
 have he : inner ℂ (Dial.mateK ν) (acts (-f) W)=inner ℂ (Dial.mateK ν) (acts f W):=by
    rw [←hp]; nth_rw 1 [hx]; unfold U₀; rw [← arum_act U false false]; nth_rw 1 [← arum_self (q:=Dial.mateK ν) U false false (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR A inert once t ν)]; exact arum_globe U false false (Tset ν) ((touchP ν) ▸ Dial.tickB ν) (tickR A inert once t ν) _ _
 rw [act_neg,inner_neg_right] at he; exact add_self_eq_zero.mp (add_eq_zero_iff_eq_neg.mpr he.symm)
lemma steel_odd (f:Mark ν)(q:AtSupport true (Finset.univ) f): Journey.compass Y i' k' M f=0:=by
 unfold Journey.compass; rw [show markedRead _ _ _ = 0 from ?_,zero_div]; unfold markedRead; simp_rw [steel_grade Y i' k' _ ((q.allV _).sector)]; simp

local notation "d_" s:max => side Y i' s
local notation "θ_" => Chi.canonical
local notation "boom" k:max =>nextMark (ho:=Λ.R.odd_side) (j:=Λ.K.j) ((Y.voyage i').X (Y.uv k')).gram (Y.voyage i').CapeT θ_ Λ.J.d ((Y.voyage i').X (Y.uv k')).wave (steps Λ.V (Y.ir i') Λ.block (Y.uv k')) k
lemma polar_fit_grows (s:ℕ) (f:Mark (side Y i' s)) {g₀:Bool}{S:Support (More (side Y i' s))} (t:legalAt Y s i' k') (h:AtSupport g₀ S f):
    let g:=Vale.apt (Y.ir i') Λ.block Λ.R.L s; let Q:= ((Y.voyage i').X (Y.uv k')).wave s; let r:=g.count.val;
    AtSupport g₀ (padded g S (r*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)) ((boom s) f):=by
 let k:= (fullness Y i' k' t.1).cap_grant
 obtain ⟨U⟩:= k.grant s t.2; obtain ⟨y,b,h₀,F0,s'⟩:= U.cap
 intro g Q r; have he:= surround g (steps Λ.V (Y.ir i') Λ.block (Y.uv k') s) Λ.K.j Q.val ((X (s+1)).J.M) Λ.R.odd_side θ_ Λ.J.d ((X (s+1)).beta) (YT s) (show Stencil.LaurentRadius Λ.K.j Λ.R.L (aliasLaw Λ) from Journey.legal Λ) F0.bill (k.branch s t.2) U.legal.1 U.legal.2 f h (tissue Y i' s) (k.aligned s t.2)
 rw [k.radius s t.2] at he; exact he
lemma step_issued (s:ℕ)(f:Mark (side Y i' s)) {g₀:Bool}{S:Support (More (side Y i' s))} (t:legalAt Y s i' k') (p:AtSupport g₀ S f): Journey.compass Y i' k' s f= Journey.compass Y i' k' (s+1) ((boom s) f):=by
 unfold Journey.compass; have he:= poly_num Λ.U ((Y.voyage i').X (Y.uv k')).gram (Y.voyage i').CapeT θ_ Λ.J.d (Y.uv k') _ _ (legal Λ) (fullness Y i' k' t.1).cap_grant (p.mono (Finset.subset_univ _)) t.2
 rw [(show markedRead f _ _=_ from he), ((Y.voyage i').X (Y.uv k')).balance s t.2.le, ((Y.voyage i').X (Y.uv k')).balance _ t.2]
lemma pay_self {s:ℕ}(z:Tapestry.Pay Y s i' k'){f:Mark (side Y i' s)}(q:AtSupport true Finset.univ f): Journey.compass Y i' k' s f=0:= by
  suffices h:∀ t:ℕ,∀{s:ℕ},∀ (e:t+s=M){f:Mark (side Y i' s)} (q:AtSupport true Finset.univ f), Journey.compass Y i' k' s f=0 from h (M-s) (Nat.sub_add_cancel z.2) q
  intro t; induction t with
  | zero=>intro s k f p; rw [Nat.zero_add] at k; subst s; exact steel_odd Y i' k' f p
  | succ t ih=>
    intro s g f p; have ht:legalAt Y s i' k':= ⟨z.1,by omega⟩
    rw [step_issued Y i' k' s f ht p]; exact ih (show t+(s+1)=M by omega) ((polar_fit_grows Y i' k' s f ht p).mono (Finset.subset_univ _))
lemma sharp_parity {s:ℕ}(p:Tapestry.Pay Y s i' k'){F:Family (tent Y H)}{S:Finset Cover}(f:InTest K₁ true S true F): sharp Y H s i' k' F=0:= pay_self Y i' k' p ((ship_box (terrain Y H (Y.ir i') s) S (f.support (momentm Y i' s))).mono (Finset.subset_univ _))
end tranche
end YM.CF.Buffered.Afterglow.Tower.QuantaCore
#print axioms YM.CF.Buffered.Afterglow.Tower.QuantaCore.sharp_parity
