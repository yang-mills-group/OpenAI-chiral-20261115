import YM.CF.Dial.Tide
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
-- general analytic Budget
abbrev Chop (ι:Type*):=∀ i:ι, ∀ {c f:Side}(G:Ratio c f), Bale c f → Op (Iota G)
variable {ι:Type*}
abbrev IndexB (L: Side)(u v:AxisT)(F: Chop ι)(a K e:ℝ)(k:ℕ) :=∀ i {N P:Side}(G:Ratio N P), G.count=L→ k≤N.val→ Crown (badge (zoneP G e)) (rope G u e) (rope G v e) a K (fun x=> F i G x.val)
def BoxD (L:Side)(u v:AxisT)(F:Chop ι):Prop:= ∃ a C e:ℝ, 0<a∧0<C∧0<e∧ ∃ k:ℕ,IndexB L u v F a C e k
variable {A B: Chop ι}{L:Side}{u v t w z:AxisT}
lemma boxify {a C e:ℝ}{k:ℕ}(h:IndexB L u v A a C e k)(p:0<a)(he:0<e): BoxD L u v A:=⟨a,max 1 C,e,p,lt_max_of_lt_left zero_lt_one,he,k,fun i _ _ G hu hv=> (h i G hu hv).books (le_max_right ..)⟩
lemma crewD {e m a:ℝ}(h:0<m)(hj:m≤e)(ha:m≤a*e): Towards (curveD G e) (badge _) (curveD G m) (badge _) (fun x=> ⟨x.val,portland G x.property hj⟩) a:=by
  let f :zoneP G m→zoneP G e:=fun x=> ⟨x.val,portland G x.property hj⟩
  refine ⟨continuous_subtype_val.subtype_mk _,rfl,rfl,fun _ _=>rfl,fun S x y=> ?_,fun b h V hs γ p=> h V hs (f ∘ γ) p⟩
  let Q:=bookK G x.val y.val S; change Q/|e|≤a*(Q/|m|); rw [abs_of_pos h, abs_of_pos (h.trans_le hj)]; apply (div_le_iff₀ (h.trans_le hj)).mpr
  calc Q= Q/m*m:=by field_simp
       _ ≤ Q/m*(a*e):=mul_le_mul_of_nonneg_left ha (div_nonneg (bk ..) h.le)
       _ = _:=by ring
lemma ropes (u: AxisT)(a b:ℝ): (rope G u a).run=(rope G u b).run:=by rcases u with ⟨b|b,k|k⟩<;> rfl
lemma neck {e m a K:ℝ}{k:ℕ}(p:0<m)(h:m≤e)(hb:IndexB L u v A a K e k): IndexB L u v A a K m k:=fun i _ _ G he hk=> (crewD G (a:=1) p h (by simpa)).bring (ropes ..) (ropes ..) (hb i G he hk) le_rfl
namespace BoxD
lemma brood (h: BoxD L u v A)(p:BoxD L w z B):∃ a C e:ℝ,0<a∧0<C∧0<e∧∃ k:ℕ,IndexB L u v A a C e k ∧ IndexB L w z B a C e k:=by
  obtain ⟨a,C,e,ha,hC,he,k,H⟩:=h; obtain ⟨b,M,d,hb,hM,hd,l,W⟩:=p; let m:=min a b; let n:=min e d; have he':0<n:= lt_min he hd
  refine ⟨m,max C M,n,lt_min ha hb,lt_max_of_lt_left hC,he',max k l,?_,?_⟩
  · intro i N P G hu hv; exact (((neck he' (min_le_left e d) H) i G hu ((le_max_left ..).trans hv)).drop (min_le_left a b)).books (le_max_left C M)
  intro i N P G hu hv; exact (((neck he' (min_le_right e d) W) i G hu ((le_max_right ..).trans hv)).drop (min_le_right a b)).books (le_max_right C M)
lemma chain (h:BoxD L u v A)(p:BoxD L v w B): BoxD L u w (fun i _ _ G x=> A i G x*B i G x):=by
  obtain ⟨a,C,e,ha,hC,he,k,H,T⟩:= h.brood p; exact boxify (k:=k) (fun i _ _ G he hg=> (H i G he hg).product (T i G he hg) ha.le) ha he
lemma add (h:BoxD L u v A)(p:BoxD L u v B): BoxD L u v (fun i _ _ G x=> A i G x+B i G x):=by obtain ⟨a,C,e,ha,hC,he,k,H,T⟩:= h.brood p; exact boxify (k:=k) (fun i _ _ G he hg=> (H i G he hg).plus (T i G he hg)) ha he
lemma sub (h:BoxD L u v A)(p:BoxD L u v B): BoxD L u v (fun i _ _ G x=> A i G x-B i G x):=by obtain ⟨a,C,e,ha,hC,he,k,H,T⟩:= h.brood p; exact boxify (k:=k) (fun i _ _ G he hg=> (H i G he hg).sub (T i G he hg)) ha he
lemma marked {f:Script ι}{u v:Bool}(h:Save L u v f): BoxD L (u,true) (v,true) (fun i _ _ G x=> f i G x.1):=by
  obtain ⟨a,C,e,p,q,r,w,H⟩:=h; refine boxify (k:=w) (C:=C) ?_ p r; intro i N P G hu hv
  let g : TopK G e → legal G e:=fun x=>⟨x.val.1,silk G x.val x.property⟩
  have ht: Towards (tempo G e) (badge _) (curveD G e) (badge _) g 1:=by
    refine ⟨(continuous_fst.comp continuous_subtype_val).subtype_mk _,rfl,rfl,fun _ _=>rfl,fun S x y=>?_,fun F h V hs γ p=>h V hs (g ∘ γ) p.fst⟩
    rw [one_mul]; apply div_le_div_of_nonneg_right (le_trans (le_add_of_nonneg_right (show 0≤ ∑ i∈ S,‖x.val.2.1 i-y.val.2.1 i‖ by positivity)) (le_add_of_nonneg_right (by positivity))) (abs_nonneg _) -- tune
  exact ht.bring (s':=rope G (u,true) e) (t':=rope G (v,true) e) rfl rfl (H i G hu hv) le_rfl
lemma one : BoxD L u u (fun (_:ι) _ _ _ _=>1):=boxify (k:=0) (fun i _ _ G u e=>Crown.ident ..) (show (0:ℝ)<1 from zero_lt_one) (show (0:ℝ)<1 from zero_lt_one)
lemma scale (h:BoxD L u v A)(f:ι→ℂ)(c:ℝ)(p:∀ i,‖f i‖≤c):BoxD L u v (fun i _ _ G x=> f i • A i G x):= by obtain ⟨a,C,e,ha,hC,he,k,H⟩:=h; exact boxify (k:=k) (C:=c*C) (fun i _ _ G u e=> ((H i G u e).scale (f i)).books (mul_le_mul_of_nonneg_right (p i) hC.le)) ha he
lemma reindex {α:Type*}(h: BoxD L u v A)(f:α→ι): BoxD L u v (fun i _ _ G x=> A (f i) G x):=by obtain ⟨a,C,e,ha,hC,he,k,H⟩:= h; exact boxify (k:=k) (fun i _ _ G u e=>H (f i) G u e) ha he
end BoxD
def upright(u:AxisT) :AxisT:=(u.1,!(u.2))
lemma ropes_cc(u:AxisT)(t : ℝ) : rope G (upright u) t=(rope G u t).reverseV:=by
  cases b:u.2
  · rw [rope,rope,upright,b]; simp only [Bool.not_false,ite_true,b,Bool.false_eq_true,ite_false]
    let W:= rod G u.1 t; change W=W.reverseV.reverseV; cases W; unfold Branch.Tag.reverseV; congr 1; funext g; apply Subtype.ext; ext; simp [ccU]
  simp [rope,upright,b]
end YM.CF.Dial
