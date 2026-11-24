import YM.CF.Pec.Frond
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N n m A B L:Side}{ho:Odd L.val} {e d a r b v:ℝ}{j k t:ℕ}
variable (G:Ratio n N)
abbrev estimateH(P:Op (Iota G))(x:Site n):ℂ:= ∑ y:Fir.St G.count,∑ i:Slot, P ((x,y),i) ((x,y),i)
lemma tuneU(P:Op (Iota G)):trout P=∑ i,estimateH G P i:=by
 change ∑ i:Iota G,P i i =_; unfold Iota; rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
lemma tuneV(P:Op (Iota G))(x:Site n)(i:Site (More N)→E): estimateH G (bore (twist ((Peaks.parcel G true d).run i) P)) x=estimateH G (bore P) x:=by
 let V:=(Peaks.parcel G true d).run i; change estimateH G (bore (twist V P)) x= _
 have hh: bore (twist V P)=twist V (bore P):=by unfold bore; rw [map_add,map_smul,map_smul,pow_two,pow_two,map_mul,pow_one,pow_one] -- tune pow lemma
 let T:=bore P; rw [hh]; unfold estimateH; refine sum_congr rfl ?_; intro s _; let j:= (x,s); let U(p:Inta G):= matter (i (touch G true p)); let L:=T.submatrix (fun v=>(j,v)) fun v=>(j,v); let g:= Equiv.refl (Inta G)
 have he: V.val= jump g fun k=>(U k).val:= warrant ..
 have hx: ((twist V T).submatrix (fun i=>(j,i)) (fun i=>(j,i)))=(U j).val*L*star (U j).val:=by
    ext a b; rw [twist_formula,he,jump_star]; change ((_*T) *_) _ _= _; rw [Matrix.mul_apply]; unfold Iota; rw [Fintype.sum_prod_type]; apply Eq.trans (sum_eq_single j _ _) -- tune
    · rw [Matrix.mul_apply]; refine sum_congr rfl ?_; intro l _; apply congrArg₂ _ ?_ (by simp [jump_apply,g]); rw [Matrix.mul_apply]; rw [Fintype.sum_prod_type]; refine Eq.trans (sum_eq_single j ?_ ?_) ?_; intro k _ hk; simp [jump_apply,g,Ne.symm hk,hk]; simp; rw [Matrix.mul_apply]; simp [jump_apply,g,L]
    · intro k _ hk; simp [jump_apply,g,hk,Ne.symm hk]
    simp
 have hg:=congrArg Matrix.trace hx; rw [Matrix.trace_mul_cycle (U j).val, show star (U j).val*(U j).val=1 from (U j).property.1,one_mul] at hg; exact hg
variable {G}
variable {D: Ratio (CSide m B) (CSide A B)}
variable (L j ho D) in
def coatG (M:Male)(P:Dress (CSide A B))(x:nomA m A B): Op (Iota D):= gate L j ho D M x (P x.1)
lemma coatPay(k:ℕ)(p:Spack j L ho a b d t)(s:0<a)(u:0<b)(h:0<d)(g:0<r)(w:0<v) :∃ f e:ℝ, 0<f ∧ 0<e ∧∀ {m A B:Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}(F:Forest T.ratio), T.ratio=ratio G→ G.count=L→t≤(CSide m B).val→∀ M:Male,∀ U:Dress (CSide A B), ReadY F G (fun i=>foot G (U (fine group F i))) r v k→ ReadY F G (coatG L ho j G M U ∘ hats F) f e k:=by
 obtain ⟨c,z,hc,hz,H⟩:= creed k s u h L; let Y:=Fintype.card (SpinIdx × Slot); let x:= min r c; let K:=v+z; have he:0<x:=lt_min g hc; have hx:0<K:=add_pos w hz
 let f:=slip k x; let A:=slip k f; have hF:0<f:=slip_pos k he; have hA :=slip_pos k hF; let q:= conductor k Y x; let T:= 2*((1+K)*K*q); let T':=2*(K*K*q); let r':=2*(T*K*conductor k Y f); let Mx:=2*(K*T'*conductor k Y f); have hv:= conductor_pos k Y he; have hh:=conductor_pos k Y hF
 have hi:0<r':=by unfold r' T q; positivity
 have hf:0<Mx:=by unfold Mx T' q; positivity
 refine ⟨slip k A,2*(Mx*r'*conductor k Y A),slip_pos k hA,(by have hp:=conductor_pos k Y hA; positivity),fun {m A B G T} F ht hG hu M U Q=>?_⟩
 let T':= unionP ∘ hats F
 have hp (F' : Coil (CSide m B) (CSide A B)→ Op (Iota G))(r0 s0:Bool)(H':Crown (badge (legal G d)) (Peaks.parcel G r0 d) (Peaks.parcel G s0 d) a b (fun i=> F' i.val)):ReadY F G (F' ∘ T') x K k:=by
    obtain ⟨S,P⟩:= H F G ht hG F' _ _ H'; exact ((HoldX.drop (⟨S,P,hz⟩:ReadY F G _ c z k) (min_le_right r c)).lift (le_add_of_nonneg_left w.le))
 have hx:= p.U M G hG hu; have hg:= tally G; let P':=hp _ _ _ (p.P M G hG hu); have hQ:= ((Q.drop (min_le_left r c)).lift (le_add_of_nonneg_right hz.le)); have hy:=slip_le k he.le
 exact (((hp _ _ _ (p.K M G hG hu)).drop hy).times ((hp _ _ _ hx).times (hp _ _ _ (p.W M G hG hu)) he hg) hF hg |>.times ((((HoldX.blank he).opP P'.minus).times hQ he hg).times (P'.drop hy) hF hg) hA hg)
lemma knit (i:Iota G)(p:Odd G.count.val): separation ((ratio G).embed (node i.1.1)) (lookM G i) ≤ 6*G.count.val:=by
 obtain ⟨⟨x,y,k⟩,b⟩:=i; let j:=node (isle G (x,y)); let A:=ratio G; change separation (A.embed (node x)) j ≤ _; have ht:=edge_t G y x p; have hp:= Corona.near A j; apply (separation_triangle (A.embed (node x)) (A.embed (A.parent j)) j).trans; rw [separation_comm _ j]; have hx : separation (A.embed (node x)) (A.embed (A.parent j))≤ G.count.val *4:= Broc.scale_span G _ _ 4 ht; have he:2* separation j (A.embed (A.parent j))≤ G.count.val:=hp; omega
lemma estimate_cost(k:ℕ)(s:0<a)(u:0<b)(L:Side)(ho:Odd L.val):∃ c w:ℝ,0<c∧0<w ∧∀ {n N:Side}{G:Ratio n N}{T:RG.StepData (More n) (More N)}(F:Forest T.ratio), T.ratio=ratio G→ G.count=L→∀ (P:Snap F→ Op (Iota G)),ReadY F G P a b k→∀ x:Site n,(ContDiffAt ℝ (↑k) (fun y=>estimateH G (bore (P y)) x) 0)∧ Beacon (clothH T F) c k (fun y=>estimateH G (bore (P y)) x) (T.ratio.embed (node x)) 0 w:=by
 let c:=slip k a; have hc:=slip_pos k s; let K:=Fintype.card (SpinIdx × Slot); let A:=2*(b*b*conductor k K a); let C:=(2*b+2*A)* Real.exp (c * (k*(6*L.val):ℕ)); have hA:0<A:=by have ht:=conductor_pos k K s; unfold A; positivity
 have hC:0<C:=by unfold C; positivity
 refine ⟨c,Fintype.card (Fir.St L)*(Fintype.card Slot*C),hc,(by positivity),fun {n M G T} F he hv P p x=>?_⟩
 let Q:= fun y:Snap F=>P y*P y; have hQ:ReadY F G Q c A k:=p.times p s (tally G); let U:=p.drop (slip_le k s.le); let V y:=bore (P y); have ht : ContDiffAt ℝ ω V 0:= (((p.glow.pow 1).const_smul _).add ((p.glow.pow 2).const_smul _)); have hy(i j:Iota G): ContDiffAt ℝ (↑k) (fun y=>V y i j) 0:=(Nacre.tort.mp ht i j).of_le le_top
 refine ⟨ContDiffAt.sum (f:=fun t: Fir.St G.count=> (fun y=> ∑ i:Slot,V y ((x,t),i) ((x,t),i))) fun i _=> ContDiffAt.sum fun j _=> hy _ _,?_⟩
 let y:= T.ratio.embed (node x)
 have hu(i:Fir.St G.count)(j:Slot): let t:=((x,i),j); Beacon (clothH T F) c k (fun y=>V y t t) y 0 C:=by
   intro t; let q:=lookM G t
   have hz: Beacon (clothH T F) c k (fun i=>P i t t) q 0 (2*b):=by simpa [c,q,Decay] using pendant (Nacre.tort.mp p.glow) U.law t t
   have hr: Beacon (clothH T F) c k (fun i=>Q i t t) q 0 (2*A):=by simpa [c,q,Decay] using pendant (Nacre.tort.mp hQ.glow) hQ.law t t
   have hS:=beacon_scale (bcoef 0) (Nacre.tort.mp p.glow t t) hz; have hR:=beacon_scale (bcoef 1) (Nacre.tort.mp hQ.glow t t) hr
   have hD {v:ℕ}(C:ℝ)(h:0≤C):|bcoef v| *C≤ C:=mul_le_of_le_one_left h (bc_norm _); unfold V bore; simp_rw [pow_one,pow_two, Matrix.add_apply, Matrix.smul_apply]; exact blink_b ((hS.mono (hD (2*b) (by positivity))).add ((Nacre.tort.mp p.glow t t).const_smul _) ((Nacre.tort.mp hQ.glow t t).const_smul _) (hR.mono (hD (2*A) (by positivity)))) (by positivity) hc (by unfold q y; rw [he,separation_comm]; exact (knit t (hv.symm ▸ ho)).trans_eq (by rw [hv])) -- slip unknown
 apply (beacon_S (s:=Finset.univ) (fun i _=>beacon_S (s:=univ) (fun j _=>hu i j) (fun j _=>hy _ _)) fun i _=> ContDiffAt.sum fun j _=> hy _ _).mono; simp only [sum_const,card_univ,nsmul_eq_mul]; rw [hv]
end YM.CF.Pec
