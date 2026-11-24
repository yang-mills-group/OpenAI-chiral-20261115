import YM.CF.Braid.Plain
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
lemma Pond.constant (a:ℂ)(M:ℕ):Pond (α:=α) M ‖a‖ (fun _=> a):= by have hp:= Pond.modes (α:=α) a 0; simp only [size,Pi.zero_apply, Int.natAbs_zero,sum_const_zero,mode_zero,one_mul] at hp; exact hp.mono le_rfl (Nat.zero_le _)
lemma no_d {v:Axis→ℝ} {i:Axis} (he:q (axes v) i ≠ 0) (A:ℝ) (F:SpanAt 0 (r+1))(h:Board M A F) (ha:0≤ A) (hp:Cycles (twist (axes v)) (r+1) F): ∃ X:SpanAt 0 (r+2),Board M (‖(q (axes v) i)⁻¹‖*A) X∧ wall locus0 X∧ ∀ p:Corn (Keys 0), cob (r+1) (twist (axes v)) X (axes p)=F (axes p):=by
 let a:= q (axes v) i; let b := a⁻¹
 let X:SpanAt 0 (r+2):=fun p j x=> b*(left ℂ (r+1) i *ᵥ fun j=> F p j x) j; refine ⟨X,?_,fun p j=> ?_, fun p=>?_⟩
 · intro j x; unfold X; simp_rw [eliminate]; split
   next hI=>
    have hp:= ((h (Exterior.remove i j hI) x).scal (parity j.val i ℂ)).scal b; exact hp.mono (by simp [parity,b,a]) le_rfl
   simp_rw [mul_zero]; exact Pond.zeros.mono (mul_nonneg (norm_nonneg _) ha) le_rfl
 · intro i x; exact i.elim0
 funext j x; have ht:twist (axes v) (axes p)=axes v:=by simp [twist,missing]; -- careful
 let Y:=fun k=> F (axes p) k x; have hv:(wedge r (q (axes v))).transpose *ᵥ Y=0:=by
    rw [←ht]; exact funext fun i=> congr_fun (congr_fun (hp p) i) x
 have hq:=cartan_remove Y (q (axes v)) i; rw [hv,Matrix.mulVec_zero,zero_add] at hq; unfold cob; rw [ht,symbol]; erw [Matrix.mulVec_smul (wedge (r+1) (q (axes v))).transpose b (left ℂ (r+1) i *ᵥ Y),hq,smul_smul]; unfold b a; rw [inv_mul_cancel₀ he,one_smul]
lemma excited {f:SheetLeg α ξ r}(h:Board M A f): JetWall 0 f:=jet_nil (A:=Real.exp M*A) (fun i x=> (h i x).analytic)
-- pricing as explicit pair M↦radius/Afactor. easier point formula
abbrev scenery (t M:ℕ):=peak t M -- X
abbrev scenery2(t M:ℕ):=peak t (1+scenery t M) -- Y
abbrev rowDr(t M:ℕ):=fock t (1+fock t M)
def paneR : (t r M:ℕ) → ℕ
| 0,_,M=>M
| t+1,r,M=> scenery t M + rowDr t (scenery2 t M + rowDr t (paneR t (r+2) (scenery2 t M)))
def palmJ (C:ℝ) : (t r M:ℕ)→ℝ
| 0,_,_=>C
| t+1,r,M=> liftCost t M + (((liftCost t M*topG 0 * liftCost t (1+scenery t M))*(1+palmJ C t (r+2) (scenery2 t M)*topG (r+3))) * (4*((scenery2 t M + rowDr t (paneR t (r+2) (scenery2 t M))):ℕ))) *topG (r+2)
lemma palm_pos(C:ℝ)(h:0≤ C)(t r M:ℕ):0≤palmJ C t r M:=by induction t generalizing r M with
 | zero=>exact h
 | succ t ih=> rw [palmJ]; have hf : 0≤ palmJ C t (r+2) (scenery2 t M):=ih ..; unfold topG liftCost; positivity
lemma vacL (v:Axis→ℝ)(t r M:ℕ)(h:C≥0)(hp:r+1+2*t>4∨∃ i:Axis,q (axes v) i≠0∧ ‖(q (axes v) i)⁻¹‖≤C)(F:SpanAt t (r+1))(ha:0≤ A)(hf:Board M A F)(hc:Cycles (twist (axes v)) (r+1) F)(hu:wall locus0 F):∃ V:SpanAt t (r+2), Board (paneR t r M) (A*palmJ C t r M) V∧ wall locus0 V∧ ∀ p:Corn (Keys t), F (axes p)=cob (r+1) (twist (axes v)) V (axes p):=by
 induction t generalizing r M A with
 | zero=>
    cases hp with
    | inl he=> refine ⟨0,fun i _=>Pond.zeros.mono (mul_nonneg ha (palm_pos C h ..)) le_rfl,fun p i=> (locus0 p).zero_mem,fun p=> funext (fun j=>?_ )⟩; have hm:= Finset.card_le_univ j.val; rw [j.property] at hm; simp at hm; omega
    | inr he=>
        obtain ⟨i,hi,H⟩:=he; obtain ⟨X,HX,Hh,Ht⟩:=no_d hi A F hf ha hc; exact ⟨X,HX.mono ((mul_le_mul_of_nonneg_right H ha).trans_eq (mul_comm ..)) le_rfl,Hh,fun p=> (Ht p).symm⟩
 | succ t ih=>
    obtain ⟨X,HX,_,HT,Hj⟩:=drift F v ha hf line_uniform (fun i j=> ((seal_tail i _).1 (hu i j)).1) hc (Or.inl (by omega)) (Or.inr rfl) (excited hf)
    let X':=headPress X; let T: Corn (Keys (t+1)) → Submodule ℂ (Run t→ℂ):= fun p=>locus0 (clipVars p)
    have U:Uniforms _ _ (stick t) T:= var_uniform fun _ _ he=>by unfold T; rw [he]
    have hv:Cycles (twist (axes v)) (r+2) X':=by
       intro p; unfold X'; rw [←plight]; funext a x; unfold headPress; rw [←Hj]; exact ((seal_tail p _).1 (hu p a)).2 x
    have hb:0≤A*liftCost t M:=mul_nonneg ha (by unfold liftCost; positivity)
    have hB:=pressP HX hb
    have hb₁: 0 ≤ A*liftCost t M*topG 0:=mul_nonneg hb (by unfold topG; positivity)
    obtain ⟨Y,HY,_,HW,Hy⟩:= drift X' v hb₁ hB U (press_wall HT) hv (Or.inl (by omega)) (Or.inr rfl) (excited hB)
    have hconv(p:Corn (Keys t)): axes (extendVar p 0)=extendVar (axes p) 0:=by ext1 ⟨i,j⟩; induction i using Fin.cases <;> simp [axes]
    let Z:SpanAt t (r+3):=fun p=>Y (extendVar p 0)
    have hz(p:Corn (Keys t)): cob (r+2) (twist (axes v)) Z (axes p)=0:=by
       have hX:X' (axes (extendVar p 0))=0:=by funext i x; simp only [X',headPress]; rw [show projected (stick t) (axes (extendVar p 0))=0 from funext fun _=>by simp [projected,axes,stick,strand]]; simp [symbol,q,wedge]
       have he:=(Hy (extendVar p 0)).symm.trans hX; funext a x; have hh:= congr_fun (congr_fun he a) x; simp only [hconv,cob,twist,miss_extend,neg_zero,zero_add] at hh; exact hh
    let N:=scenery2 t M; have hd:0 ≤ (A*liftCost t M*topG 0)* liftCost t (1+scenery t M):=mul_nonneg hb₁ (by unfold liftCost; positivity)
    obtain ⟨W,hW,Wh,Wp⟩:= ih (r+2) N (hp.imp_left (by omega)) Z hd (woody HY) hz (by intro p i; have he:=HW (extendVar p 0) i; unfold T at he; rw [hconv,extends_drop] at he; exact he)
    let W' : SheetLeg (Keys (t+1)) (Run t) (r+4) := fun p=> W (clipVars p); have HW':wall T W':=fun p i=>Wh (clipVars p) i; let U':=palmJ C t (r+2) N
    have hw' := too v (f:=W') (tale hW) (mul_nonneg hd (palm_pos C h t (r+2) N))
    let L:=Y-cob (r+3) (twist (axes v)) W'; let R:= N+rowDr t (paneR t (r+2) N); let c':= A*liftCost t M*topG 0*liftCost t (1+scenery t M); let B:= c'+c'*U'*topG (r+3); have hh: Board R B L:= Board.sub (Board.mono HY le_rfl (Nat.le_add_right ..)) (Board.mono hw' le_rfl (Nat.le_add_left ..)); have hB:0≤ B:=add_nonneg hd (mul_nonneg (mul_nonneg hd (palm_pos C h t (r+2) N)) (by unfold topG; positivity)) -- tune
    obtain ⟨J,hJ,_,Hg,hg⟩ := press_pref L hB hh (excited hh) (fun p i=>(T p).sub_mem (HW p i) (wall_cob (twist (axes v)) HW' p i)) (by
       intro p hs; let q:=clipVars p; have he:p=extendVar q 0:=by
          conv_rhs=>rw [←hs]
          exact (extends_back p).symm
       rw [he,hconv]; funext i x; simp only [L,Pi.sub_apply,cob,W',twist,extends_drop,miss_extend,neg_zero,zero_add]; exact sub_eq_zero.mpr (congr_fun (congr_fun (Wp q) i) x))
    let S:= X-cob (r+2) (twist (axes v)) J
    refine ⟨S,?_,fun p i=> ?_, fun p=>?_⟩
    · have he:= too v hJ (mul_nonneg hB (by positivity)); apply Board.mono (Board.sub (Board.mono HX le_rfl (show _ ≤ paneR (t+1) r M from Nat.le_add_right ..)) (Board.mono he le_rfl (by exact Nat.le_add_left ..))) _ le_rfl
      exact le_of_eq (by rw [palmJ]; unfold B U' R c' N; push_cast; ring)
    · apply (seal_tail p _).2; refine ⟨(lineTail p).sub_mem (HT p i) (wall_cob _ Hg p i), fun z=>?_⟩
      change headPress S (axes p) i z=0; unfold S; rw [press_sub,plight]; simp only [Pi.sub_apply]; apply sub_eq_zero.mpr; change X' _ _ _=_; have he:cob (r+2) (twist (axes v)) L=cob (r+2) (twist (axes v)) Y:=by unfold L; rw [cob_sub,cob_zero,sub_zero];
      rw [Hy, ← he]; unfold cob; rw [hg]
    unfold S; rw [cob_sub,cob_zero,sub_zero,Hj]
end YM.CF.Braid
