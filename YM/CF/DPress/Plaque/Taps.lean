import YM.Extra.WILSON_STARTUP.Face
/-! supports and plaquette coupons of the A2E transport. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.DPress.Plaque
open Function Finset Lattice RG WilsonStartup
open scoped Topology Classical
variable {n:Side}(o:Site n)
-- four positively based plaquettes on that coordinate (support roots).
abbrev Rings:= (univ:Finset (Face (Per n))).filter fun i=> o∈touched i
abbrev Bases(v:PlaqAxes):Finset (Site n):={o,o-step v.val.1,o-step v.val.2,o-step v.val.1-step v.val.2}
lemma trusts (i:PlaqAxes)(U:Site n):o∈ touched (U,i)↔U∈Bases o i:=by
 rw [four_visit]; simp only [Bases, mem_insert, mem_singleton]; constructor
 · rintro (p|p|p|p); exact Or.inl p.symm; exact Or.inr (Or.inl ((eq_sub_iff_add_eq).2 p.symm)); exact Or.inr (Or.inr (Or.inr (by rw [p]; abel))); exact Or.inr (Or.inr (Or.inl ((eq_sub_iff_add_eq).2 p.symm)))
 rintro (p|p|p|p); exact Or.inl p.symm; exact Or.inr (Or.inl ((eq_sub_iff_add_eq).1 p|>.symm)); exact Or.inr (Or.inr (Or.inr ((eq_sub_iff_add_eq).1 p|>.symm))); exact Or.inr (Or.inr (Or.inl (by rw [p]; abel)))
lemma stick(x:Site n)(i:Axis): separation (x+step i) x≤1:= by unfold separation; rw [add_comm x,add_sub_cancel_right]; exact pdist_step _
lemma bill(i:Face (Per n)){x y:Site n}(h:x∈ touched i)(u:y∈touched i): separation x y≤2:=by
 rw [four_visit] at h u; obtain ⟨z,p,v⟩:=i; let a: Site n:= z+step p.1; let b: Site n:= z+step p.2; let c:=a+step p.2
 change x∈({z,a,c,b}:Finset (Site n)) at h; change y∈({z,a,c,b}:Finset (Site n)) at u
 have he:separation a z≤1:=stick ..; have hv:separation b z≤1:=stick ..; have hp:separation c a≤1:=stick ..; have hq:separation c b≤1:= by rw [show c=b+step p.1 from add_right_comm ..]; exact stick .. -- tune
 have hh :∀ (x y:Site n),separation x y ≤ 1→ separation y x ≤ 1:=fun x y p=> (separation_comm y x).trans_le p
 have Ha: separation z a≤1:=hh a z he; have Hb:= hh b z hv; have Hc:=hh c a hp; have Hd:=hh c b hq
 have hk : separation c z≤2:= (separation_triangle c a z).trans (by omega); have hz:separation z c ≤2:=(separation_comm _ _).trans_le hk
 have hxy : separation a b≤2:= (separation_triangle a z b).trans (by omega); have hyx:separation b a≤2:= (separation_comm _ _).trans_le hxy
 simp only [mem_insert,mem_singleton] at h u; rcases h with h|h|h|h <;> rcases u with t|t|t|t <;> rw [h,t] <;> first
 | simp only [separation_self]; omega
 | omega
variable (i:PlaqAxes)
lemma paycheck (m:2 ≤ n.val): (Bases o i).card=4:=by
 let a:= i.val.1; let b:= i.val.2; let x:Site n:= step a; let y: Site n:= step b; letI : Fact (1<n.val):=⟨m⟩; have ht(j:Axis):(step j:Site n)≠0:=fun h=> by have hv:=congrFun h j; simp [Per] at hv
 have hp: a ≠ b:= i.property.ne; have hu:x≠y:=fun h=>by have t:=congrFun h a; simp [x,y,Lattice.step,hp,Per] at t
 have hv:x+y≠0:= fun h=>by have v:=congrFun h a; simp [x,y,Lattice.step,hp,Per] at v
 have hx:=ht a; have hy:=ht b; change x ≠ 0 at hx; change y≠ 0 at hy
 have jant(x y:Site n)(h:y≠0):x≠x-y:=fun e=> h (add_left_cancel (a:=x) (by rw [(eq_sub_iff_add_eq).1 e,add_zero]))
 change ({o,o-x,o-y,o-x-y}:Finset (Site n)).card=4; rw [card_insert_of_notMem,card_insert_of_notMem,card_insert_of_notMem,card_singleton]
 · simp
   exact jant o x hx
 · simp [hu]
   exact jant (o-x) y hy
 · simp [←sub_add_eq_sub_sub]
   exact ⟨jant o x hx,jant o y hy,jant o (x+y) hv⟩
lemma ringSum {M:Type*}[AddCommMonoid M] (f:Face (Per n) → M): ∑ i∈Rings o,f i =∑ v:PlaqAxes,∑ x∈Bases o v,f (x,v):=by unfold Rings; rw [sum_filter,Fintype.sum_prod_type,sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [←sum_filter]; congr; ext; simp [trusts]
lemma knownC(m:2 ≤ n.val): (Rings o).card=Fintype.card PlaqAxes*4:=by have h:= ringSum o (fun _=> (1:ℕ)); simp [paycheck _ _ m] at h; exact h
end YM.CF.DPress.Plaque
