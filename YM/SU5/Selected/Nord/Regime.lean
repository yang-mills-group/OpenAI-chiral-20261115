import YM.SU5.Selected.Nord.Ether
/-! # Telescoping purchase. real signed pressure lower adjacent steps at high observation scale. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x z : ℝ} {D C R0 : ℝ → ℝ} (h' : ℝ) {delay : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {N0 B1 : ℕ} {q : Chi}
variable {n T' : ℕ → ℕ} {P : Prescription R B}
namespace LocalLimit
open Preparation Chene Pitching Focus
variable {Λ:Preparation}{Z:(s:Side)→ Scree.Loom s → Prop} (Y: Course Λ Z)(Q:Scooped Λ)
abbrev β_time (i k s:ℕ):=(RootBook Y i k s).beta
abbrev blood(i k s:ℕ):=(RootBook Y i k s).J.M
abbrev age(i s:ℕ):= Λ.Ctor (Y.ir i) s
abbrev RefH (k s:ℕ) := Λ.V.L.H (k-s)
def marks (i k s:ℕ):ℝ:= Perks.schedule Λ.L (More (age Y i s)) (RefH (Λ:=Λ) (Y.uv k) s) (β_time Y i k s)+ Fragment.token Λ.K.j (age Y i s) (blood Y i k s)
lemma haunt (s i k:ℕ)(h:s<Y.uv k): blood Y i k s= upMale Λ.R.L Λ.R.odd_side (blood Y i k (s+1)):=by
 let t:=Y.voyage i; let z:=Y.uv k; let H:= t.X z; let V:= Λ.W.arm (Y.meter.large.trans t.funds) z; have he(q:ℕ)(w:q≤z): (RootBook Y i k q).J= V.Q q:= (H.pull.owns q w).taste.symm; unfold blood; rw [he s h.le, he (s+1) h]; exact (V.pass s h).grown
lemma heightRoom (i s:ℕ): Λ.U.roundZ≤(age Y i s).val:= Λ.J.gran.trans ((Y.voyage i).ownership s).size
lemma age_above(B:ℕ) :∀ᶠ s in atTop,∀ i:ℕ, B≤(age Y i s).val:=by
 filter_upwards [(Work.E01.radiusB_tendsto.comp (turnover Λ)).eventually_ge_atTop B] with s u i; let h:=Y.meter.clear (Y.voyage i).funds 0 s; let A:=age Y i s; have ht:100*(1+ (radiusB (hat Λ.R.L Λ.x s))) ≤ (More A).val:= h.1.size
 change radiusB _≥B at u; change _ ≤ A.val; change _ ≤ A.val *2 at ht; omega
lemma hOne (P:Preparation): 1 ≤ P.K.j:= by rw [P.kJ]; omega
lemma pad_bill : ∀ᶠ s in atTop,∀ i:ℕ,Kea.Pad Λ.K.j (age Y i s):=by
 obtain ⟨d,H⟩:= Kea.gave Λ.K.j (hOne _); exact (age_above Y d).mono fun s p i=> H (age Y i s) (val_e ..) (p i)
include Q
lemma futureCost (δ:ℝ)(p:0<δ): ∀ᶠ s in atTop,∀ i k,s<Y.uv k → |(RootBook Y i k s).v.re-(RootBook Y i k (s+1)).v.re-(marks Y i k (s+1)-marks Y i k s)| ≤ δ*sites (Λ.Ctor (Y.ir i) (s+1)):=by
 filter_upwards [(tendsto_add_atTop_nat 1).eventually (pad_bill Y),truthUp Y Q δ p] with s v ht i k t; let X:=age Y i s; let F':=Λ.V.L.H (HighAge Y s k+1); let f:= Fragment.token Λ.K.j X (blood Y i k s); let g:= Fragment.token Λ.K.j (age Y i (s+1)) (blood Y i k (s+1)); have pZ:replacement Y i k s=f -g:=by
    unfold f replacement; rw [haunt Y s i k t]; have hx:=heightRoom Y i s; exact Fragment.route Λ.U (blood Y i k (s+1)) Λ.dpos (hOne _) Λ.W.pearl Λ.V.note hx _ rfl _ Λ.V.gate _ _ (v i)
 have hp: RefH (Λ:=Λ) (Y.uv k) (s+1)=Λ.V.L.H (HighAge Y s k):=congrArg Λ.V.L.H (show Y.uv k-(s+1)=_ from (by unfold HighAge; omega))
 have hq: RefH (Λ:=Λ) (Y.uv k) s=F':=congrArg Λ.V.L.H (show Y.uv k - s=HighAge Y s k+1 by unfold HighAge; omega)
 obtain a:= ht i k t; dsimp only at a; rw [pZ] at a; unfold marks; rw [hp,hq]; change |(_ :ℝ)-(_+g-(_+f))| ≤  _; rw [show Perks.schedule _ _ _ _ + g- (_+f)= (Perks.schedule _ _ _ _ - Perks.schedule _ _ F' _ - (f-g)) from ?_] -- tune
 · exact a
 abel
omit Q
lemma tokenLo {s i:ℕ}(M:Tulip.Male)(p:Kea.Pad Λ.K.j (age Y i s)) : let g:= Fragment.token Λ.K.j (age Y i s) M; g ≤ 0 ∧ 0 < Kea.angel (mesh (Y.ir i) Λ.R.L s) Λ.U M ∧ Real.log (Kea.angel (mesh (Y.ir i) Λ.R.L s) Λ.U M)=g:=by
 let N:=age Y i s; let A:= Kea.angel (mesh (Y.ir i) Λ.R.L s) Λ.U M; have hp:=heightRoom Y i s; have ht:0<A:= Kea.angel_p Λ.W.pearl Λ.V.note hp (hOne _) Λ.dpos M p; have he: A ≤1:=by
    unfold A Kea.angel Kea.AMP; rw [Signal.Sparkle.LocalPlane.free1]; apply (norm_inner_le_norm ..).trans; rw [(tickB _).2,(sea_g hp 1 (Fragment.blank_ok Λ.dpos.le) M).2,one_mul]
 intro g; have hy:g=Real.log A:= Fragment.present Λ.U M Λ.dpos (hOne _) hp; rw [hy]; exact ⟨Real.log_nonpos ht.le he,ht,rfl⟩
private lemma algebra_h (T Q τ K:ℝ)(p:0≤K)(t:T≤4*K)(w:0≤T)(u v z:ℝ)(h:u ≤ Q)(e:T*τ ≤z)(hx:0≤v) : T*u-v/2*z ≤ K*(4*(|Q|+v/2*|τ|)) := by
 calc
 _ ≤ T* (|Q|+ v/2 * |τ|) := by rw [mul_add]; nlinarith only [mul_le_mul_of_nonneg_left (h.trans (le_abs_self Q)) w, mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left (neg_abs_le τ) w) e) (show 0≤ v/2 by positivity)]
 _ ≤ _ := le_trans (mul_le_mul_of_nonneg_right t (by positivity)) (le_of_eq (by ring))
omit Y in
lemma cap_gauge (Λ:Preparation):∃ C:ℝ,∀ (i:Side)(b:ℝ)(v:1 < i.val) (z:1≤b) (n:ℕ), Perks.schedule Λ.L i (Λ.V.L.H n) b ≤ C* Perks.bulk i:=by
 let G:=SU.group; let T:= logFlat Λ.L; let a:= min Λ.V.W.parcel 1; have hp:0<a:=lt_min Λ.V.W.reserve zero_lt_one; let m:= Fintype.card G.ColorIndex; let A:= 4*(|T| + (m:ℝ) /2*|Real.log a|); refine ⟨(A:ℝ),?_⟩; intro i b v z n; let B':=Λ.V.L.H n; let W:= (Next.Rank.Axial.axle i); let V':= Perks.bulk i; let D:= Trunk.Chene i B' W.trunks; let N:=(Perks.shoots i:ℝ);
 have hv:= Λ.V.L.roof n; have ht:= hv.2.1 i; let P0:= Real.log (Next.SectorChange.spare Λ.L b); have h₀:P0 ≤ T:= by unfold P0 T; rw [spare_formula Λ.L Λ.chart.scale (zero_lt_one.trans_le z)]; refine sub_le_self _ ?_; exact mul_nonneg (by positivity) (Real.log_nonneg z)
 have h':a^Fintype.card W.Free≤D:=Trunk.grain v B' a _ (Trunk.legal _ W) hp (min_le_right ..) ((show FreeResolvent.Gap (B'.metric.acts i) _ from ⟨fun z=>(ht.uniform.1 z).1⟩).mono (min_le_left _ 1)) ht.symmetric.1; have hy:=Real.log_le_log (pow_pos hp _) h'; rw [Real.log_pow] at hy; have hx: Perks.quantity i≥ Perks.shoots i:= Fintype.card_le_of_injective Subtype.val Subtype.val_injective; change N*P0- Perks.atoms0 G /2*Real.log D ≤ _; rw [_root_.mul_comm A]; exact algebra_h N T (Real.log a) V' (Nat.cast_nonneg _) ((Nat.cast_le (α:=ℝ)|>.mpr hx).trans_eq (Perks.bulk_edge i)) (Nat.cast_nonneg _) P0 (m:ℝ) _ h₀ hy (Nat.cast_nonneg _)
lemma marks_rent :∃ C:ℝ, ∀ᶠ s in atTop,∀ i k,s≤Y.uv k → marks Y i k s ≤ C*sites (age Y i s):=by
 obtain ⟨C,p⟩:=cap_gauge Λ; refine ⟨C,?_⟩; filter_upwards [pad_bill Y, (turnover Λ).eventually_ge_atTop 2] with s v t i k β; have he:= ((Y.voyage i).X _).pull.sift s β; have hh:1 ≤ (RootBook Y i k s).beta:= (show (1:ℝ)≤ hat Λ.R.L Λ.x s/2 from (by linarith)).trans he.1
 unfold marks; rw [← volumesBB]; have hz: 1 < (More (age Y i s)).val:= Nat.lt_of_lt_of_le (by norm_num :(1:ℕ) < 1*2) (Nat.mul_le_mul_right 2 (age Y i s).property)
 exact le_trans (by have hp:= (tokenLo Y (blood Y i k s) (v i)).1; exact add_le_of_nonpos_right hp ) (p (More (age Y i s)) _ hz hh _)
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.marks_rent
#print axioms YM.CF.Py.Rate.LocalLimit.futureCost
