import YM.CF.Vale.Inca
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v:ℕ}{f g a b d:ℝ}{B m:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}
lemma amplit(m B L:Side)(j:ℕ):m.val≤(cell m B L j).val:=by
 induction j with
 | zero => unfold cell; rw [show mesh m L 0=m from by simp [mesh]]; change _≤ m.val*2*B.val; exact (show _≤m.val*2 from by omega).trans (Nat.le_mul_of_pos_right _ B.property)
 | succ j ih => rw [grows]; change _ ≤ (cell m B L j).val*L.val; exact ih.trans (Nat.le_mul_of_pos_right _ L.property)
namespace Gold
variable (A:Gold K P R W) (H:Reward D K C R P W) (h:C.i≤m.val)
-- sweep downward preserving upper stages.
structure Last (A:Gold K P R W) (D:Grasp U B e)(C:Credit)(m:Side)(v:ℕ) where
 Q:(i:ℕ)→ Interest (cell m B P.L i)
 shift:ℕ→ℝ
 top:Q v=vanilla _
 sound(i):InterestX C _ (Q i)
 pass(i:ℕ)(h:i<v): A.ticket m D C (v-1-i) i (Q i) (Q (i+1)) (shift i)
include h H
lemma path_w(x:ℕ):x≤v→∃ Q:(i:ℕ)→Interest (cell m B P.L i),∃ t:ℕ→ℝ, Q v=vanilla _ ∧ (∀ i,InterestX C _ (Q i)) ∧ ∀ i,i<v → v ≤ i+x → A.ticket m D C (v-1-i) i (Q i) (Q (i+1)) (t i):=by
 induction x with
 | zero => intro _; exact ⟨fun i=> vanilla _, 0,rfl,fun i=>naturalC .., fun i r l=> (by omega)⟩
 | succ x ih=>
    classical
    intro p; obtain ⟨Q,t,hq,ht,hP⟩:= ih (by omega); let i:=v-1-x; have hi:i<v∧i+x+1=v:=by unfold i; omega
    obtain ⟨N,z,Z⟩:= A.earnest H i x (h.trans (amplit ..)) (Q (i+1)) (ht _)
    let P(i':ℕ)(w:i'≠i): update Q i N i'=Q i':=update_of_ne w _ _
    refine ⟨update Q i N,update t i z,(P v (by omega)).trans hq,fun j=>?_,fun j p q=>?_⟩
    · by_cases e:j=i; subst j; rw [update_self]; exact Z.courage; rw [P j e]; exact ht j
    by_cases e:j=i
    · subst j; rw [P (i+1) (by omega), update_self, update_self,show v-1-i=x by omega]; exact Z
    rw [P j e,P (j+1) (by omega),update_of_ne e]
    exact hP j p (by omega)
lemma gives(v:ℕ):Nonempty (Last A D C m v):=by
 obtain ⟨Q,t,hp,ht,hv⟩:= A.path_w H h v le_rfl; exact ⟨⟨Q,t,hp,ht,fun i p=>hv i p (by omega)⟩⟩
end Gold
variable {S:Gold K P R W}
-- all interval Valued and pure estimates
lemma sum_cost (hv:1 ≤ K.C)(g:Even K.j)(p:Stamped K.j P.L P.odd_side U)(h:Spack K.j P.L P.odd_side a b d k)(hB:Pearl D)(x:0<a)(f:0<b)(y:0<d)(t:0<e)(hz:4≤P.L.val)(S:Gold K P R W)(C:Credit) :∃ z:ℝ,0<z ∧ ∃ N:ℕ,∀ {m: Side}, N≤m.val →∀(v:ℕ)(A:S.Last D C m v),∀(i j:ℕ),i+j≤v→ |(∑ w∈range j,A.shift (i+w))- (j:ℝ)*(spiceM*Real.log P.L.val)| ≤ z:=by
 obtain ⟨d',v,hd,hv',H⟩:= cover_u 2 K P
 have ht:= K.width; have hy:= S.lobby ▸ P.order_cut; have hh:0<K.C:=zero_lt_one.trans_le hv
 obtain ⟨n,r,hr,hp⟩:=plateau hB p t (by omega) hz h x f K.j K.j K.bind.penalty hy hy K.bind.penalty_pos C.f C.F C.u C.U C.b C.B K.η K.C d' v C.P C.posf C.posF C.posu C.posU C.posb C.posB ht hh hd hv' C.posP
 let N:=n+D.roundZ+k+W.n
 refine ⟨r,hr,N,fun {m} u w A i j e'=>?_⟩
 have hm(r:ℕ): N≤(cell m B P.L r).val:=u.trans (amplit ..)
 have hE(r):W.n ≤ (More (cell m B P.L r)).val:=by have he:=hm r; unfold N at he; change _ ≤ (cell m B P.L r).val*2; omega
 refine hp (fun j=>mesh m P.L (i+j)) (fun j=>A.Q (i+j)) (fun j=>A.shift (i+j)) j (fun l _=> (A.sound _).leanJ) (fun l _=> ⟨(show n ≤ N from by unfold N; omega).trans (hm (i+l)), val_e ..⟩) (fun l h=>(A.pass (i+l) (by omega)).fiscal) ?_
 refine ⟨fun l x' =>?_⟩; have he:= S.follow_X g p h t y ((show D.roundZ+k+W.n ≤ N from by unfold N; omega).trans (hm (i+l))) (A.pass (i+l) (by omega)) (fun F z p=> H (S.op _ _) F _ (S.pace _ (hE _) _) rfl (S.lent _) S.lobby W.bar (S.mood _) p); exact he
end YM.CF.Vale
