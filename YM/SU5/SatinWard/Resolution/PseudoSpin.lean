import YM.SU5.SatinWard.Resolution.Symbol

/-!
# Pseudoscalar sector: PH
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
local notation "EndC"=> Op SU.Slot

/- transitive with no grade-switch. -/
lemma even_ways (j:Axis):∃ s:Signed,s∈ Loomed∧detX s=false∧s.perm 0=j:=by
 let A:=inPlane*outPlane; let B:= exchangePlane; have ht:A∈ Loomed:= mul_mem in_l out_l
 have hp:B∈ Loomed:= exchange_l
 fin_cases j
 · exact ⟨1, Loomed.one_mem,det_i,rfl⟩
 · exact ⟨A,ht,det_classp,by unfold A; decide⟩
 · exact ⟨B,hp,det_exchange,by unfold B; decide⟩
 exact ⟨B*A,mul_mem hp ht,by rw [det_p,show detX A=false from det_classp,show detX B=false from det_exchange]; rfl,by unfold A B; decide⟩

lemma enigma_eq (D:Axis→Pal)(h:∀ i,D i∈mind_B)
    (H: ∀ s:Signed,s∈ Loomed→detX s=false→∀ i:Axis,
        sign s i • castPal false false (spinU false s) (D (s.perm i))=D i) (i:Axis):
    D i=petal i⊗ₖ spaX (D 0) 0:=by
 have hp (j:Axis):D j=petal j⊗ₖ spaX (D j) j:=by
    apply invariant_slice j (D j) (spin_bin _ (h j))
    intro c p g t w; have ht:= H c p w j; rw [sign,t,g] at ht; simp at ht; exact ht -- tune Equiv
 have hV(j:Axis):spaX (D j) j=spaX (D 0) 0:=by
    obtain ⟨s,u,t,v⟩:= even_ways j; have h:=castPet (s:=s) (U:=spinU false s) (a:=false) (b:=false) (by simpa only [t] using (spinZ false s)) 0 (spaX (D j) j); rw [v] at h
    have hx:= H s u t 0
    rw [v,hp j, h, hp 0, sign_hush] at hx; cases g:s.flip 0 <;> apply spa_i 0 <;> simpa only [g,hush_true,hush_false,Bool.false_eq_true,↓reduceIte,windX,neg_neg] using hx
 exact (hp i).trans (by rw [hV i])

structure WindingSpin (A:EndC): Prop where
 color(g:SU.E):Commute A (matter g).val
 realW : cc A=A

def axialSchedule (A:EndC): Dome:= (0,fun i=>petal i⊗ₖ A,fun i=>petal i⊗ₖ star A)

lemma axial_transform (A:EndC)(H:cc A=A)(s:Signed)(a:Bool):
  coinArc s a (detX s) (spinU a s) (axialSchedule A)= hush a (1:ℝ) • axialSchedule A:=by
 let b:=detX s; let U:=spinU a s; let X:=castPal a b U; let P₁(i:Axis):= petal i; let Hx(A:EndC)(g:cc A=A)(a:Bool):windX a A=A:=by cases a; rfl; exact g
 have Hv₁(i:Axis)(g:b=false)(K:EndC)(t:cc K=K):
     sign s i • X (P₁ (s.perm i)⊗ₖ K)= hush a (1:ℝ) • (P₁ i⊗ₖ K):=by
    unfold X; rw [show castPal a b _ _= _ from castPet (spinZ a s) i K, show detX s = false from g,Hx K t,sign_hush]; cases a<;>cases s.flip i<;> simp [P₁]
 have Hv₂(i:Axis)(g:b=true)(K:EndC)(t:cc K=K):
     sign s i • X (P₁ (s.perm i)⊗ₖ K)= hush a (1:ℝ) • (P₁ i⊗ₖ star K):=by
    unfold X; rw [show castPal a b _ _= _ from castPet (spinZ a s) i K, show detX s = true from g,Hx K t,sign_hush]; cases a<;>cases s.flip i<;> simp [P₁]
 have ht: cc (star A)=star A:=by rw [cc_star,H] -- tune
 apply Prod.ext; · change castPal a b U (0:Pal)= _ • 0; simp [castPal,Thera.jazz,win_z]
 cases g:b <;> apply Prod.ext <;> funext i
 · change sign s i • X ((if b then (axialSchedule A).2.2 else (axialSchedule A).2.1) (s.perm i))=_; simp only [if_neg (show ¬ b = true by rw [g]; decide)]; exact Hv₁ i g A H
 · change sign s i • X ((if b then (axialSchedule A).2.1 else (axialSchedule A).2.2) (s.perm i))=_; simp only [if_neg (show ¬ b = true by rw [g]; decide)]; exact Hv₁ i g (star A) ht
 · change sign s i • X ((if b then (axialSchedule A).2.2 else (axialSchedule A).2.1) (s.perm i))=_; simp only [if_pos g]; exact (Hv₂ i g (star A) ht).trans (by rw [star_star]; rfl)
 change sign s i • X ((if b then (axialSchedule A).2.1 else (axialSchedule A).2.2) (s.perm i))=_; simp only [if_pos g]; exact Hv₂ i g A H

lemma WindingSpin.star_color (A:EndC)(H:WindingSpin A)(g:SU.E):Commute (star A) (matter g).val:=by
 have h:= congrArg star (H.color g⁻¹).symm.eq; rw [show ↑(matter g⁻¹)=star (↑(matter g):EndC) from congrArg Subtype.val (map_inv matter g),star_mul,star_mul,star_star] at h; exact h


lemma axial_sector (n:Side)(D:Dome):
    (D.1∈mind_B ∧ D.2∈ mind_C∧∀ s∈twoPlanes n,costDome s D=(pseudoCharacter n).sgn s • D) ↔ ∃ A:EndC,D=axialSchedule A∧ WindingSpin A:=by
 constructor
 · rintro ⟨p,u,h⟩
   have he(s:Signed)(g:s∈ Loomed)(b:Bool): coinArc s b (detX s) (spinU b s) D=hush b (1:ℝ) • D:=by
      let t:Sweep n:=⟨s,0,b⟩; have hp:=h t⁻¹ ((twoPlanes n).inv_mem g);
      rw [costDome,inv_inv] at hp; exact hp
   let F:=spaX (D.2.1 0) 0; let G:=spaX (D.2.2 0) 0
   have hz:D.1=0:=by
      let s:=allFourFlip; have ht:= congrArg Prod.fst (he s allFour_mem false); let U:=spinU false s; have w:detX s=false:=det_allFour; rw [w,hush_false,one_smul] at ht; exact minus_unique _ (ht.symm.trans (flip_negates (show JetS s false false U from (by simpa only [w] using (spinZ false s))) D.1 (spin_bin _ p))) -- align
   have p₁(i):D.2.1 i=petal i⊗ₖ F:=enigma_eq _ (fun i=>(jetsBin _ u i).1) (fun s p g j=>by have ht:=he s p false;rw [g,hush_false,one_smul] at ht; exact congrFun (congrArg (fun A:Dome=>A.2.1) ht) j) i
   have p₂(i):D.2.2 i=petal i⊗ₖ G:=enigma_eq _ (fun i=>(jetsBin _ u i).2) (fun s p g j=>by have ht:=he s p false;rw [g,hush_false,one_smul] at ht; exact congrFun (congrArg (fun A:Dome=>A.2.2) ht) j) i
   refine ⟨F,Prod.ext hz (Prod.ext (funext p₁) ?_),⟨?_,?_⟩⟩; swap
   · intro g; apply (commutes_petal 0 F g).1; rw [←p₁ 0]; exact (jetsBin _ u 0).1.2 g
   · let s:=Signed.mirror 0
     have ht:detX s = true:=det_t 0; have a:=he s (mirror_l _) false
     rw [ht,hush_false,one_smul] at a; have h:= congrFun (congrArg (fun A:Dome=> A.2.2) a) 0
     change sign s 0 • castPal false true (spinU false s) (D.2.1 (s.perm 0))= D.2.2 0 at h
     rw [p₁,sign_hush, castPet (a:=false) (b:=true) (s:=s) (U:=spinU false s) (by simpa only [ht] using (spinZ false s)), p₂] at h
     simp only [show s.flip 0=true from rfl,hush_true,hush_false, neg_neg] at h; have t:star F=G:=spa_i 0 h
     funext i; change D.2.2 i=petal i⊗ₖ star F; rw [p₂,t] -- clockwise
   let U:=spinU true 1; have a:=he 1 Loomed.one_mem true
   rw [det_i,hush_true,neg_one_smul] at a; have h:=congrFun (congrArg (fun A:Dome=> A.2.1) a) 0
   change sign 1 0 • castPal true false U (D.2.1 ((1:Signed).perm 0))= -(D.2.1 0) at h
   -- after p₁ both sides.
   rw [p₁ ((1:Signed).perm 0), castPet (s:=1) (U:=U) (a:=true) (b:=false) (by simpa only [det_i] using (spinZ true 1))] at h
   rw [p₁ 0] at h
   apply spa_i 0; rw [sign_hush,Signed.one_flip, hush_false, hush_true,hush_false] at h; exact neg_injective h
 rintro ⟨A,rfl,w⟩
 have hz : ∀ (v:Axis)(F:EndC), (∀ g:SU.E,Commute F (matter g).val) → petal v⊗ₖ F∈mind_B:=fun v F h=> And.intro (show culm _ = _ from pet_normShape v F) (fun i=>(commutes_petal ..).2 (h i))
 refine ⟨mind_B.zero_mem, And.intro ?_ ?_,fun s a=>?_ ⟩
 · exact fun i=> hz i A w.color
 · exact fun i=> hz i (star A) (w.star_color A) -- projection order
 exact axial_transform A w.realW ..
end YM.CF.QuadClock
