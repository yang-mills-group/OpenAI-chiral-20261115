import YM.CF.Tarn.Cane
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
variable(q:Chi)(d α:ℝ)(l:ℕ)
def rugG(P:Tab S):FileM c G:=fun j=> aria fun s:Signed=>∑ i∈ hoop S s j, tilT T x q d α l P s i
lemma rug_k(i:Site c)(P P':Tab S)(p:Kind S P P' (pavilion (horn x l) i))(ht:Ready T x)(hp:1000 ≤radiusB x): rugG T x q d α l P i=rugG T x q d α l P' i:=by
 unfold rugG; apply congrArg aria; ext1 s; refine Finset.sum_congr rfl fun v hv =>?_ ; have he:= (mem_filter.mp hv).2; funext Z; have hz(V:Config G c): loreG T x q d α l s v (bunk S P V)=loreG T x q d α l s v (bunk S P' V):=by refine crisp T x q d α l v ht hp s ?_; rw [show herald S s v=i from he]; exact ⟨fun _ _=>Iff.rfl,p.site,fun i h=>p.edge i (h (mem_insert_self ..)),KinT p,fun _ _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 unfold tilT; rw [hz,hz]
open AnalyticBridge.GaussianFieldAlignment Channels Locations
lemma rug_o(K:Teller G)(p:K.Funds S T)(i:Site c)(P:Tab S)(b:Site c)(s:Signed)(V:Config G c): rugG T x q d α l (dial S s b P) i (pull s b V)= rugG T x q d α l P (affine s b i) V:=by
 unfold rugG aria; simp only [Pi.smul_apply,Finset.sum_apply]; apply congrArg ((Fintype.card Signed:ℂ)⁻¹ • ·); rw [← Equiv.sum_comp (Equiv.mulLeft s) (fun y=>∑ j∈hoop S y (affine s b i), tilT T x q d α l P y j V)]; refine Finset.sum_congr rfl fun y _=>?_ ; let E:=lawn S (Channels.offset s b y); refine Finset.sum_bij (fun j _=>E j) ?_ (fun _ _ _ _ l=> E.injective l) ?_ (fun i _=>til_tr T x q d α l s y b P i V p)
 · intro j hj; exact mem_filter.mpr ⟨mem_univ _,(Arena.herZ b y s j).symm.trans (congrArg (affine s b) ((mem_filter.mp hj).2))⟩
 intro j hj; refine ⟨E.symm j,?_,E.apply_symm_apply j⟩; apply mem_filter.mpr ⟨mem_univ _,?_⟩; apply (StepData.sendSites s b).injective; change affine s b _= _; rw [Arena.herZ, show lawn S (Channels.offset s b y) _=j from E.apply_symm_apply j]; exact (mem_filter.mp hj).2
lemma rug_p(P:Tab S)(i:Site c)(s' A:ℝ)(ht:0≤A)(hx:0<s')(hv:2≤n)(hz:∀ j k,CakeF (tilT T x q d α l P k j) (herald S k j) (horn x l) n s' A):let a:=about S.patch.L 0; let V:= rugG T x q d α l P i; CakeF V i (horn x l) n s' (a*A) ∧ cFoot 2 (satX V):=by
 intro a V; suffices h:Urge V i 2 1 (horn x l) n s' (a*A) 0 by exact ⟨h.1,h.2.1⟩
 refine urgeM _ ?_ hx hv (by omega); intro u
 let P' := hoop S u i; refine (urgeSum P' (A:=A) ?_ hx hv (by omega:1 ≤ n)).under (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hoop_c S u i)) ht) (by rw [mul_zero]) le_rfl
 intro j p; have ht:= hz j u; rw [show herald S u j=i from (mem_filter.mp p).2] at ht; exact Foot.change (kleur _ _ ht.toAtom (show 1 ≤ n by omega) (by unfold tilT; simp only [sub_self]) (ht.ledger 0 (by simpa using hx)).smooth Thera.yet_one) le_rfl (by decide) le_rfl ht
open Souk
lemma toZ (P:Tab S)(u:ℝ)(v:Mast G c)(he:Fire T x P.1 P.2 l u n C v) : let y:=u • v; let V:= satU G u v; let R:=Hors.cart x S.patch.L; let F:= flute P.1 (sol S T P.2 x P.1 l) 1 y
 averaged (fun s:Signed=>∑ i:Along S,loreG T x q d α l s i (bunk S P V))= inLoop (safeD T.up (Stores.till x)).loop P.1 F - draft α (safeD T.down R) T.low (tint G (Body 1 c) y):=by
 intro y V R F; let L:=Stores.till x
 let A(s:Signed):=vX T P.1 P.2 s (y,(0:Fish _)); let B(s:Signed):=Push.Uniform.signedFine P.1 F s
 let Y(s:Signed):=∑ i, king ∅ T.down T.low L S.patch.L.val x (A s) i; let X(s:Signed):= uncut (safeD T.down R).loop (A s); let Z(s:Signed):=uncut (safeD T.up L).loop (B s);
 have hv(s:Signed): Y s= quadratic T.low (safeD T.down R) (A s):=by unfold Y quadratic; exact sum_congr rfl fun i _=>kin_q S.patch.L.val S.patch.L.property T.down T.low x (A s) i
 have hp(s:Signed):(∑ i:Along S,loreG T x q d α l s i (bunk S P V))= -(α*quadratic T.low (safeD T.down R) (A s))+(Z s-X s):=by
    unfold Along; simp_rw [Fintype.sum_sum_type]; unfold loreG TaleX; simp only [sum_const_zero,zero_add,add_zero,sum_neg_distrib,← mul_sum]; rw [← hv]; have hu: pull s 0 ((bunk S P V).sent x T q d l 0) = B s:=by
       rw [originY T x _ _ rfl rfl rfl he]; unfold fX B Jazz pulse Function.comp; unfold F flute; simp only [one_smul]; change Push.Uniform.signedFine P.1 (meetVar y ((0:Fish (Key P.1 G))+ _)) s= Push.Uniform.signedFine _ _ _; rw [zero_add]; rfl
    rw [hu,neg_mul, ← sub_eq_add_neg]; rfl -- tune sums
 simp_rw [hp]; rw [av_add,av_sub]; unfold draft secondTerm Precision.loop Patch.average averaged; rw [sum_neg_distrib,←mul_sum]; unfold Z inLoop; change _ = (Fintype.card Signed:ℝ)⁻¹* (∑ s,Z s) - (α * ((Fintype.card Signed:ℝ)⁻¹ * ∑ s, quadratic T.low _ (A s))+ (Fintype.card Signed:ℝ)⁻¹ * ∑ s,X s); ring
lemma rug_s(P:Tab S)(u:ℝ)(v:Mast G c)(he:Fire T x P.1 P.2 l u n C v) (ht:Fire T x P.1 P.2 l u n C 0): let U:=rugG T x q d α l P; let V:= satU G u v; let X(y:Mast G c):= inLoop (safeD T.up (Stores.till x)).loop P.1 (flute P.1 (sol S T P.2 x P.1 l) 1 y)-draft α (safeD T.down (Hors.cart x S.patch.L)) T.low (tint G (Body 1 c) y)
 (∑ i,U i V)= (X (u • v):ℂ)-(X 0:ℂ):=by
 intro U V X; let N(s:Signed)(V:Config G c):=∑ i,loreG T x q d α l s i (bunk S P V); have hp: averaged (fun s=>N s V)=X (u • v):= toZ T x q d α l P u v he; have hv: averaged (fun s=>N s 1)=X 0:= by
    have h: averaged (fun s=>N s (satU G u (0:Mast G c)))=X (u • 0):=toZ T x q d α l P u 0 ht; simpa only [satU,smul_zero,show facadeX G (0:Mast G c)=1 from by simp [facadeX]] using h
 rw [←hp,←hv]; unfold U rugG aria; simp only [Pi.smul_apply, Finset.sum_apply,smul_eq_mul]; rw [← mul_sum,sum_comm]; simp_rw [hoop_sum]; -- tune f arg
 unfold tilT N averaged; simp only [sum_sub_distrib,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv,Complex.ofReal_natCast]; ring
end
end YM.CF.Tarn
