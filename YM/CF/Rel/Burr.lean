import YM.CF.Rel.Dots
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
abbrev pcost(m r:ℕ):=m*(4*(2*r))
def cSize(m M:ℕ):=rowDr m (M+(m+1)) -- m meaning subtract1
lemma pressV {F:CurRun (m+2)→ Space (m+1)→ℂ}(v:Axis→ℝ)(he:∀ i,Pond r A (F i))(h:0≤ A): ∃ B:ℝ, ∀ i,Pond (cSize m r) B (clipP F v i):=by
 let V:= strands (Embedding.refl (Keys (m+1))); let M:= inlet F V
 have hv:Board (r+(m+1)) (A*topG 1^(m+1)) M:=fun i x=> con_s (Embedding.refl (Keys (m+1))) h (fun j=>F (Fin.cons i j)) (fun i=>he _) _
 have hw:=too v hv (mul_nonneg h (by unfold topG; positivity)); refine ⟨A*topG 1^(m+1)*topG 1,fun i=>?_⟩
 have hp:clipP F v i=fun p=>cob 1 (Braid.twist (axes v)) M p (i 0) (Fin.tail i):=by
    ext1 p; unfold clipP; rw [fromCurl_cons]; simp only [cardR,Fin.cons_zero,Fin.tail_cons]; rfl
 rw [hp]; exact hw _ _
variable {F:FileM n G}{W:KitM G n (m+2)}{v:Axis→ℝ}{k:Site n}
def paysV(m r l:ℕ):ℝ:= ((plot (cSize m (pcost (m+1) r)))^(m+1):ℕ)*(plot (2*l))^(m+1)
lemma lensF (h:shapeV k F)(hp:Push.Loops.Matches (axes v) k)(ht:nerve 0 r W)(hc:0≤ A)(hf:0 ≤ C)(hW:∑ i,‖W i‖ ≤ A)(hg:Prox F (m+2) C)(hx:∀ i,Atom (F i) i l)(hy:∀ i,ContDiffAt ℝ (↑(m+2:ℕ):WithTop ℕ∞) (satX (F i)) 0)(hs:∀ V,cake (m+2) (satX (F 0)) V=∑ p, engages W p V)(hz:2*cSize m (pcost (m+1) r)<n.val)(a: SpotG G (m+2))(i:Run (m+2)):
 Pond (cSize m (pcost (m+1) r)) (paysV m r l*C) (clipP (breathL W k a) v i):=by
 obtain ⟨B,H⟩:= pressV (m:=m) v (forda W ht k a · hW) hc; exact (stocks (H i) hz (scan_F hx hy hg hf k h v hp W hs i a) (by positivity)).mono (le_of_eq (by unfold paysV; push_cast; ring)) le_rfl
-- complementary hypothesis on local function f independent via lifted affine tests. existence can show later. no reliance on W choice.
def Ridge(f:SpaceX G n)(l:ℕ):Prop:= ∀ (i:CurRun 2) (s:SpotG G 2), Disjoint (i 0).val (i 1).val→∃ y:Fin 2→InputZ G n, (∀ a:Fin 2,∀ x∈hallmark (n:=n) 0 l,sumH G (y a) x=if x.2=i a then jewelG G (s a) else 0) ∧ cake 2 (satX f) y=0
lemma moneyV (f: SpaceX G n)(W:KitM G n 2)(hp:nerve 0 r W)(hg:Ridge f r)(hs:∀ V,cake 2 (satX f) V=∑ p,engages W p V)(a:SpotG G 2):∀ i:CurRun 2, Disjoint (i 0).val (i 1).val→ breathL W 0 a i 0=0:=by
 intro i hi; obtain ⟨Y,hY,H⟩:=hg i a hi
 have hx : (∑ p:Disk n 2, engages W p Y)=0:=(hs _).symm.trans H
 rw [←hx,d_sum]; unfold breathL; simp_rw [mode_constant,one_mul,grabG,cell_duality 0 (_:Site n),cell_origin,one_mul]; rw [sum_comm]; refine sum_congr rfl fun p _=> sum_congr rfl fun z _=>?_ ; rw [Fintype.sum_eq_single i] -- maybe reorders
 · unfold engages; let v:= diskP (m:=1) p z i; by_cases hh: v∈Pots 0 r 2
   · congr 1; ext1 t; rw [hY]; have he(t:Fin 2): (v t).2=i t:= by induction t using Fin.cases <;>simp [v,diskP];
     exact (if_pos (he _)).symm -- tune
     exact Fintype.mem_piFinset.mp hh _
   rw [hp _ hh]; rfl
 intro j hj; unfold engages; let v:=diskP (m:=1) p z j; by_cases hV:v∈Pots 0 r 2
 · obtain ⟨l,hl⟩:= Function.ne_iff.mp hj; apply ContinuousMultilinearMap.map_coord_zero _ l; rw [hY l _ (Fintype.mem_piFinset.mp hV _)]; rw [if_neg _]; have he(t:Fin 2): (v t).2= j t:=by induction t using Fin.cases<;>simp [v,diskP];
   change (v l).2 ≠ _; rw [he]; exact hl
 rw [hp _ hV]; rfl
end YM.CF.Rel
