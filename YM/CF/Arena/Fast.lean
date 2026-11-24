import YM.CF.Arena.Yale
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
lemma parL (z:Signed)(i:Along S)(p:Monk G S)(h:p.z=0)(hp:herald S z i∉ p.key.dome (horn x l))(v:Ready T x)(hz:1000 ≤ radiusB x): (dense T x q d l β z i p:ℂ)=bale T (p.park,p.k) q x d l z i p.V :=by
 let Q:=bunk S (p.park,p.k) p.V
 -- issue U difference. synthetic nohole U use A.U; holds none. compare THEN remove. Beat requires all U,
 let H:Monk G S:={p with key:=bareStores S}
 let X:=pavilion (horn x l) (herald S z i); have he:Beat p H X:=by
    refine ⟨fun j k=>?_ ,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
    have hQ:j∉ p.key.place:=fun u=>hp (halo_spec.mpr ⟨j,u,(separation_comm ..).trans_le ((theatre ..).mp k)⟩); change (_↔ j∈(bareStores S).place); simp only [iff_false_intro hQ]; simp [bareStores, Stores.place]
 have hv:dense T x q d l β z i p=dense T x q d l β z i H:=calm z i v hz (Subset.refl _) he
 rw [hv]; have ht : H.sent x T q d l β= Q.sent x T q d l 0:=by
    have hv:H.bush x= Q.bush x:=funext fun i=> False.elim ((notChilled S Q.park x i.val) i.property); change landed x H.key H.park H.V (H.bush x) (H.fuel x T q d l β)=landed x H.key H.park H.V (Q.bush x) (Q.fuel x T q d l 0); rw [oasisN T q x d l (M:=H) h,oasisN T q x d l (M:=Q) rfl,hv]
 change (stars _ _ H _ _ _ _ _ _:ℂ)=(stars _ _ Q _ _ _ _ _ _:ℂ); rw [bluff q x d l T H z h,bluff q x d l T Q z rfl,ht]
lemma atomS (j:ℕ)(t:Monk G S)(p:t.z=0)(hp:l+76≤j)(h:Ready T x)(ht:1000 ≤ radiusB x)(A:Tab S→DirP c)(b:ℕ): let E:=t.key.dome (j*radiusB x); let U(s:Signed):=rush x t.key s j;
 (averaged fun s=>∑ i∈ U s,dense T x q d l β s i t) = Complex.re (∑ i,issued x j b (fun v:Tab S=>fame T v q x d l) A t.key (t.park,t.k) i t.V):=by
 intro E U; rw [← Finset.sum_apply,grantsU]; let F(i:Site c):=fame T (t.park,t.k) q x d l i; let X(z):ℝ:= ∑ i∈U z,dense T x q d l β z i t; have he(i:Site c): (if i∈E then (0:SpaceX G c) else F i) t.V= if i∈E then 0 else F i t.V:=by split<;>rfl
 have hv(z)(i)(p':i∈U z): bale T (t.park,t.k) q x d l z i t.V=(dense T x q d l β z i t:ℂ):= (parL z i t p (fun u=>(mem_filter.mp p').2 (farther (Nat.mul_le_mul_right _ hp) u)) h ht).symm
 let Y(i:Site c):= if i∉E then F i t.V else 0; have hh: (∑ i:Site c,Y i)= (averaged X:ℂ):=by
    unfold Y; rw [←sum_filter]; unfold F fame; simp_rw [Pi.smul_apply,Finset.sum_apply,smul_eq_mul]; rw [←mul_sum,sum_comm]; unfold averaged; simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast, Complex.ofReal_sum]; apply congrArg ((Fintype.card Signed:ℂ)⁻¹ * ·); refine Finset.sum_congr rfl fun i _=>?_ ; unfold heed X; simp_rw [Finset.sum_apply]; rw [Complex.ofReal_sum]; let Z:=univ.filter (fun y:Site c=>y∉E)
    have hV : (∑ y∈ Z,∑ j∈ hoop S i y,bale T (t.park,t.k) q x d l i j t.V)=∑ j∈ U i,bale T (t.park,t.k) q x d l i j t.V:=by unfold hoop; simp_rw [sum_filter]; rw [sum_comm]; unfold U rush; rw [sum_filter]; refine Finset.sum_congr rfl fun j _=>?_ ; simp [Z,E]
    rw [hV]; exact Finset.sum_congr rfl fun j u=>hv i j u
 change averaged X=_; rw [Finset.sum_apply]; change _=(∑ i:Site c, (if i∈ E then (0:SpaceX G c) else F i) t.V).re; simp_rw [he]; rw [show (∑ i:Site c, if i∈E then (0:ℂ) else F i t.V)=∑ i:Site c,Y i from by simp [Y],hh, Complex.ofReal_re]
end YM.CF.Arena
