import YM.CF.Fixed.Mantle
import YM.CF.Fixed.Snag
import YM.CF.Ups.Nobel

/-!
Bridge to actual FiniteGaugeData layouts. No method for period extension here; for every
 `MeterQ.ridge` authentication, carry normalization and pressure charges independently.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 750000
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor Jet Vol Rel Cascade Fief Yaw Pig Wray Lich.Muster Push.AbsoluteSums Iva Eire Jade
open CF.Fixed CF.Fixed.Extensive CF.Fixed.Rift CF.Mint RoeWL Graph Girt
variable{N B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d e η z g A B':ℝ} {j k k' m n l j' :ℕ}(V:Grace K R L){x β:ℝ}
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)

open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
structure Way (x:ℝ)(M:Side)(l:ℕ) where
 val:Month x a i p N0 V W
 tip: val.q ≤ M.val
 main:ℕ→ℝ
 E:Vestal M B R.L
 Y:Cape M B R.L
 Q:ℕ→Haro.SpaceM
 tilt:ℕ→ℝ
 scale:Brioche V a p i N0 val _ tip l main J q h R0 δ E Y Q tilt
local notation "Kω"=> Way V a p i N0 J q h R0 δ
variable {M:Side}(Y:Way V a p i N0 J q h R0 δ x M l)
local notation "Xρ" j:max=> hat R.L x j
namespace Way
include Y
lemma wears(j:ℕ)(u:j≤ l): Mantle (x:=hat R.L x j) V J h (Vale.mesh M R.L j) (Y.E j) (Y.Y j):=by
    let F:=Y.scale; let A:=Y.E j; let R' :=Xρ j; have hv: (A.p)=Y.val.a j:= (F.note.owns j u).width.symm
    let U1:= Y.scale.note.note j u; let T:= Y.scale.note.owns j u; have he': A.funds=K.top.clip:=T.fund.symm
    let h:= (F.roof j).paid; exact ⟨(Y.val.clear Y.tip 0 j).1.size,F.close j u,he',by rw [←(show _=(Y.E j).funds from T.fund),← (show _=(Y.E j).path from T.path)]; exact V.L.mood _, hv ▸ (Y.val.boot j).1,J.gran.trans (F.roof j).size,T.taste ▸ ((W.arm ..).sound _),U1.lot_p le_rfl le_rfl,U1.tone,U1.buoy,U1.nite,{h with paid:= fun i=>(h.paid i).shrink J.hr.le},hv ▸ F.pole j⟩
lemma postZ (k)(u:k≤l) : star (partitionZ (Y.E k) U (Y.Y k)) = partitionZ (Y.E k) U (Y.Y k):=by
  rw [Y.scale.balance k u]; have he: (Y.E l).v=0:= by rw [Y.scale.note.boot]
  have hx:= Mantle.centered V J h (wears V a p i N0 J q h R0 δ Y l le_rfl); rw [he] at hx; simp only [neg_zero,Complex.exp_zero,one_mul] at hx
  obtain ⟨u,v⟩:=hx; rw [←v]; exact Complex.conj_ofReal u
lemma climb_safe (k)(_u:k≤l)(A:Pane (cell M B R.L k))(g:flags (Y.val.a k).threshold A=∅):Safe (Fixed.Rift.Loft _ A) := by
   let z: Orbit (cell M B R.L k):=(A,Classical.arbitrary _); let r:= Y.scale.roof k; let D:=r.paid; let F:= Y.Y k; have hv:Roof _ J.k d J.n F:={D with paid:=fun i=>(D.paid i).shrink J.hr.le}
   have hw:Guard A d:= (show F z=A from Robes.solar z F hv (Y.val.a k) (Y.scale.pole k) g) ▸ hv.paid z; exact Phase.wiel_ok (anticut (cell ..)) U.baseY hw
end Way

variable (H:Month x a i p N0 V W) (D:MeterQ V a p i N0 J q h R0 δ x H)
lemma Way.span (X:SpanPS V a p i N0 J q h R0 δ x l): Nonempty (Way V a p i N0 J q h R0 δ x (oYY V N0 J x) l):=⟨⟨X.val,X.tip,X.main,X.E,X.Y,X.Q,X.tilt,X.scale⟩⟩
include D in
lemma wide_s (M:Side)(v:J.h ≤ M.val)(pM:H.q ≤ (M*N').val)(hM:61≤(M*N').val): ∃ S:∀ l:ℕ,Way V a p i N0 J q h R0 δ x (M*N') l, (∀ i,(S i).val=H) ∧ ∃ (Y:Cape (M*N') B R.L)(ρ:ℕ→ℝ),(∀ j,(S j).Y=Y) ∧ (∀ j,0<ρ j) ∧ ∀ (l j:ℕ), j<l→ ‖Complex.exp ((S l).E (j+1)).v‖ * ρ j ≤ ‖Complex.exp ((S l).E j).v‖:=by
  obtain ⟨U0,b,bQ,hP,E⟩:= D.ridge M v pM hM
  choose X' Z C Zc Y γ p' qJ RX using E; let S(i):= (show Kω x (M*N') i from ⟨H,pM,X' i,Z i,U0,C i,Zc i, p' i,Y i,D.tint,D.pole,qJ i,hP,RX i⟩); exact ⟨S,fun i=> rfl, U0, b, fun i=>rfl,bQ,γ⟩ -- shadow p' i h etc

-- Along fixed-x cutoff history for ANY physical periods, construct test.
local notation "Lρ" => R.L
lemma issue_height (hx:0<x):∀ᶠ l:ℕ in atTop,∀ (M:Side)(Y:Way V a p i N0 J q h R0 δ x M l)(t C:ℝ),0<C→1 ≤ t → ∀ f, Motive (cell M B R.L l) (Y.val.a l) f → ¬ DirectT (Y.val.a l) C t (1/2) f:=by
  have hu:0< Vale.billX (Lρ):= by have hx:=billx_T V; unfold ν_PS at hx; linarith
  -- crude even linear lower for Nval, enough against area ∼ N³/x_hat. no rate assumption on M.
  let y:=hat R.L x; let H(i):ℝ:=tollHelps (cell 1 B R.L i); let c:=Rift.chip/32; have hc:0<c:= by unfold c; have ht:=chip_p; positivity
  have he:Tendsto y atTop atTop:= tendsto_atTop_add_const_left atTop _ (tendsto_natCast_atTop_atTop.atTop_mul_const hu)
  
  have ht(i:ℕ)(m:Side):i ≤ (cell m B R.L i).val:=by
    have ht':=(show i ≤ ((R.L^i).val) from Vale.huge R.L (by have h:=V.tallX; omega) _); apply le_trans ht'; change (R.L^i).val ≤ m.val * (R.L^i).val * 2 * B.val; exact Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ m.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
  have hp: Tendsto (fun i:ℕ=>c*(i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.const_mul_atTop hc
  -- area_cost ≥ (c/2 * i)^3 /16 * (cap threshold half)^2≥ c'* i. directly eventual via nlinarith polynomial.
  let D:= x+ Vale.billX R.L; let F'(i:ℕ):= Real.sqrt (y i); let A:= c^3/(2^3 *64*D); have hD:0<D:= add_pos hx hu; have hA:0<A:= by unfold A; positivity
  have hW:= sizeK.tempo R.L|>.spine; have hX:= tendsto_natCast_atTop_atTop.const_mul_atTop hA; filter_upwards [(hW.comp he).eventually (ge_mem_nhds chip_p),hp.eventually_ge_atTop 2,hX.eventually_gt_atTop (Real.log 9),eventually_ge_atTop (5:ℕ)] with l xh tQ w lP m Y t C g tg f fK E

  let z:= Y.val.a l; let N:=cell m B R.L l; have hN:2<N.val:=lt_of_lt_of_le (by omega:2<l) (ht _ _); let i' := (Vale.mesh m R.L l)*B; have hv: N.val=2*i'.val:= RP.suff ..; let θ:=temp (y l); have hh:z.threshold=θ:=(Y.val.boot l).1; have ht':0<θ:=hh ▸ z.threshold_pos
  apply no_color z hv (by omega) (Way.climb_safe V a p i N0 J q h R0 δ Y l le_rfl) (θ/2) (by positivity) ((half_le_self ht'.le).trans (show θ≤_ from xh)) (by linarith only [hh]) t (zero_lt_one.trans_le tg) ?_ C g f fK E
  apply lt_of_lt_of_le w
  set z':=F' l with hz
  have hxP:0<y l:= hx.trans_le (Vale.crown ..); have he :0<z':= Real.sqrt_pos.mpr hxP; have hv:z'⁻¹≤ θ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
  have hu: c*l≤tollHelps N:= by apply mul_le_mul_of_nonneg_left _ hc.le; exact_mod_cast (ht l m)
  have hn := min_area ((show 2≤ c*l from tQ).trans hu)
  have ht:Rift.hearth N (θ/2)≥ A*l :=by
    unfold Rift.hearth; let X:=(area_t N:ℝ); have hb:c*l/2 ≤ X:=(div_le_div_of_nonneg_right hu zero_le_two).trans hn -- goal uses ascent
    have hvp:= Vale.pitch R.L; have hj:1 ≤(l:ℝ):=by exact_mod_cast (by omega:1≤l)
    have hk:y l≤ D*l:=by unfold y D hat; nlinarith only [mul_le_mul_of_nonneg_left hj hx.le] -- hx shadow x replaced; fix
    have hf:z'^2=y l:=Real.sq_sqrt hxP.le
    have ht : z'*θ≥1:=by field_simp at hv; linarith
    -- recover
    have hz0 : 1 ≤ D*l*θ^2:=by
      apply le_trans (b:= y l*θ^2) _ (mul_le_mul_of_nonneg_right hk (sq_nonneg _)); rw [←hf,←mul_pow]; exact one_le_pow₀ ht
    have hL:0<(l:ℝ):=zero_lt_one.trans_le hj
    have hp: 1/(D*l)≤θ^2:= by apply (div_le_iff₀ (by positivity : 0<D*l)).mpr; nlinarith only [hz0]
    change A*l ≤ X^3*((θ/2)^2/16); calc
      _ ≤ c^3/(2^3 *64*D)*(l*l) := by unfold A; gcongr; exact le_mul_of_one_le_right hL.le hj -- syntax
      _ = (c*l/2)^3*(1/(D*l)/64):= by field_simp
      _ ≤ (c*l/2)^3*(θ^2/64):= by gcongr
      _ ≤ X^3*(θ^2/64):=by gcongr
      _ = _:= by ring

  apply le_trans ht; exact le_mul_of_one_le_left (by unfold Rift.hearth; positivity) tg -- eventual
end YM.CF.Py
