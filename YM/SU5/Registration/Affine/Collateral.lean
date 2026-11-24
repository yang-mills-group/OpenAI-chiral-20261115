import YM.SU5.Voyager.Cinder
import YM.SU5.Registration.Rise.Flying
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3200
set_option maxHeartbeats 260000
noncomputable section
open Filter Function
open scoped InnerProductSpace BigOperators Topology NNReal ENNReal ComplexOrder Classical
namespace YM.SatinRegistration

/-!
  ## Landing the (116) price in compression norm

  Basic operations for control over all THE characters in the installation. The maps
  live in *dependent* operator spaces. No uniform SOT asked here. Use with pose
  prices before changing both height and character (not after integrating and
  identifying only a.e.).
-/
variable {J ι I:Type*}
abbrev AllBills (b:ι→Type*) [∀ i, Norm (b i)] (s:Filter J)(X:J→∀ i,b i)(z:ℝ):Prop:=∀ᶠ j in s,∀ i,‖X j i‖ ≤ z
def OnTab {b:ι→Type*}[∀ i, Norm (b i)] (s:Filter J)(X:J→∀ i,b i): Prop:=∃ z≥ (0:ℝ), AllBills b s X z
lemma OnTab.later {b:ι→Type*}[∀ i, Norm (b i)]{s:Filter J}{l:Filter I}{f:I→J}{X:J→∀ i,b i}(p:Tendsto f l s)(h:OnTab s X): OnTab l (X∘f):=by obtain ⟨a,v,h⟩:=h; exact ⟨a,v,p.eventually h⟩
section less
variable {b:ι→Type*}[∀ i,PseudoMetricSpace (b i)]
variable {s:Filter J}{X Y Z : J→∀ i,b i}{r q:ℝ}
abbrev UpTo (s:Filter J)(X Y:J→∀ i,b i)(r:ℝ):Prop:=∀ᶠ j in s,∀ i,dist (X j i) (Y j i) ≤ r
def Agrees (s:Filter J)(X Y:J→∀ i,b i):Prop:=∀ r:ℝ,0<r→ UpTo s X Y r
lemma UpTo.mono' (p:UpTo s X Y r)(t:r≤q): UpTo s X Y q:= p.mono fun i h j=> (h j).trans t
lemma UpTo.chain (p:UpTo s X Y r)(v:UpTo s Y Z q): UpTo s X Z (r+q):=(p.and v).mono fun i p j=> (dist_triangle _ (Y i j) _).trans (add_le_add (p.1 j) (p.2 j))
lemma UpTo.backwards (p:UpTo s X Y r): UpTo s Y X r:=p.mono fun i p j=> (dist_comm ..).trans_le (p j)
lemma Agrees.symm (p:Agrees s X Y): Agrees s Y X:= fun r e=> (p r e).backwards
lemma of_eq (v:X=ᶠ[s] Y): Agrees s X Y:=fun r t=>v.mono (fun j p i=>by rw [p]; exact (dist_self _).le.trans t.le)
lemma Agrees.trans (p:Agrees s X Y)(v:Agrees s Y Z) : Agrees s X Z:=fun r t=>(add_halves r) ▸ (p (r/2) (half_pos t)).chain (v (r/2) (half_pos t))
lemma Agrees.refl (X:J→∀i,b i): Agrees s X X:= of_eq (Eventually.of_forall fun i=>rfl)
lemma UpTo.comps {l:Filter I}{f:I→J}(p: UpTo s X Y r)(h:Tendsto f l s): UpTo l (X∘f) (Y∘f) r:=h.eventually p
lemma Agrees.comps {l:Filter I}{f:I→J}(p: Agrees s X Y)(h:Tendsto f l s): Agrees l (X∘f) (Y∘f):=fun r t=>(p r t).comps h

-- criterion for price uniformly in the dependent bundles. Forward continuity already in arity. allows process with independent reindexes
lemma Agrees_point {V:∀ i,b i}(p:Agrees s X (fun _=>V)) (i:ι) : Tendsto (fun j=> X j i) s (𝓝 (V i)):= Metric.tendsto_nhds.mpr (fun r z=> (p (r/2) (half_pos z)).mono (fun j p=>(p i).trans_lt (half_lt_self z)))
lemma Agrees_uniform {b:Type*}[PseudoMetricSpace b] {X:J→ι→b}{x:ι→b}: Agrees s X (fun _=>x) ↔ TendstoUniformly X x s:=by
 rw [Metric.tendstoUniformly_iff]; constructor <;> intro p ε h
 · exact (UpTo.backwards (p (ε/2) (half_pos h))).mono fun j p i=>(p i).trans_lt (half_lt_self h)
 apply UpTo.backwards (b:=fun _ :ι=>b) (X:=fun _=>x) (?_); exact (p ε h).mono (fun i p j=> (p j).le)
-- Using even just approximate constant at each r. No continuity assertion on its pose.
lemma learns_price [s.NeBot] {V:∀ i,b i}(p:∀ i:ι,Tendsto (fun j=> X j i) s (𝓝 (V i)))(h:∀ r:ℝ,0<r→∃ Y:∀ i,b i, UpTo s X (fun _=>Y) r): Agrees s X (fun _=>V):=by
 intro r e; let c:=r/2; obtain ⟨Y,h⟩:=h c (half_pos e); let X':=fun _ :J=>Y
 have hv:UpTo s X' (fun _=>V) c:= Eventually.of_forall fun j i=> le_of_tendsto (tendsto_const_nhds.dist (p i)) (h.mono fun j v=>(dist_comm ..).le.trans (v i))
 exact (add_halves r) ▸ h.chain hv
end less
section prices
variable {b:ι→Type*}[∀ i,SeminormedAddCommGroup (b i)]
variable {s:Filter J}{X Y Z V' : J→∀ i,b i}{r q:ℝ}
lemma UpTo.normed : UpTo s X Y r ↔ AllBills b s (X-Y) r:=by simp only [AllBills,UpTo,dist_eq_norm]; rfl
lemma OnTab.zero : OnTab s (fun (_:J) i=>(0:b i)):=⟨0,le_rfl,Eventually.of_forall fun i j=> (norm_zero).le⟩
lemma OnTab.neg (p:OnTab s X):OnTab s (-X):=by obtain ⟨B,v,h⟩:=p; exact ⟨B,v,h.mono fun i h j=> (norm_neg _).le.trans (h j)⟩
lemma OnTab.together (p:OnTab s X)(v:OnTab s Y): OnTab s (X+Y):=by
 obtain ⟨V,u,v⟩:= v; obtain ⟨B,x,p⟩:=p
 exact ⟨B+V,add_nonneg x u,(p.and v).mono fun i h j=>(norm_add_le ..).trans (add_le_add (h.1 j) (h.2 j))⟩
lemma OnTab.rotate (p:OnTab s X)(v:Agrees s X Y): OnTab s Y:=by
 obtain ⟨B,h,p⟩:=p
 refine ⟨B+1,add_nonneg h zero_le_one,(p.and (v.symm 1 zero_lt_one)).mono fun i h j=> ?_⟩
 exact (norm_le_norm_sub_add (Y i j) (X i j)).trans ((add_le_add ((dist_eq_norm (Y i j) (X i j)) ▸ h.2 j) (h.1 j)).trans_eq (add_comm ..))
lemma UpTo.plus (p:UpTo s X Y r)(v:UpTo s Z V' q) : UpTo s (X+Z) (Y+V') (r+q):=(p.and v).mono fun i h j=> (dist_add_add_le ..).trans (add_le_add (h.1 j) (h.2 j))
lemma Agrees.plus (p:Agrees s X Y)(v:Agrees s Z V') : Agrees s (X+Z) (Y+V'):=fun r h=>(add_halves r) ▸ (p (r/2) (half_pos h)).plus (v (r/2) (half_pos h))
variable {w z:J→ι→ℂ}
lemma OnTab.scaled [∀ i, NormedSpace ℂ (b i)] (p:OnTab s X)(h:OnTab s (fun j i=> w j i)): OnTab s (fun j i=> w j i • X j i):=by
 obtain ⟨B,h',h⟩:=h; obtain ⟨C,u,p⟩:=p
 exact ⟨B*C,mul_nonneg h' u,(p.and h).mono fun j h i=> (norm_smul ..).trans_le (mul_le_mul (h.2 i) (h.1 i) (norm_nonneg _) h')⟩
lemma Agrees.scaled [∀ i, NormedSpace ℂ (b i)] (p:Agrees s X Y)(v:Agrees s (fun j i=> w j i) (fun j i=> z j i))(u:OnTab s X)(t:OnTab s (fun j i=> w j i)) : Agrees s (fun j i=> w j i • X j i) (fun j i=> z j i • Y j i):=by
 obtain ⟨B,h,u⟩:=u; obtain ⟨C,g,t⟩:=t.rotate v
 intro r e; let d:=r/(B+C+1); have h':0<d:=by unfold d; positivity
 filter_upwards [p d h',v d h',t,u] with i p v t u j
 rw [dist_eq_norm] -- at goal but not forall def unfolded? maybe rw at * fails
 let x:=X i j; let y:=Y i j
 rw [show w i j • X i j-z i j • Y i j=(w i j-z i j) • x + z i j • (x-y) by rw [sub_smul,smul_sub]; dsimp only [x,y]; abel]
 refine (norm_add_le ..).trans ?_; rw [norm_smul,norm_smul]; have he: d*(B+C+1)=r:= div_mul_cancel₀ _ (by positivity); exact (add_le_add (mul_le_mul ((dist_eq_norm (w i j) (z i j)) ▸ (v j)) (u j) (norm_nonneg _) h'.le) (mul_le_mul (t j) ((dist_eq_norm (X i j) (Y i j)) ▸ p j) (norm_nonneg _) g)).trans (by linarith only [h',he]) -- v j etc if rw not? remove early

lemma OnTab.of_agreement (p:Agrees s X (fun _ i=>0)): OnTab s X := OnTab.zero.rotate p.symm
end prices
section products
variable {b:ι→Type*}[∀ i,SeminormedRing (b i)]
variable {s:Filter J}{X Y Z U : J→∀ i,b i}{r q:ℝ}
lemma OnTab.itself (h:∀ i:ι,‖(1:b i)‖≤1) : OnTab s (fun (_:J) i=>(1:b i)):=⟨1,zero_le_one,Eventually.of_forall fun i=>h⟩
lemma OnTab.prod (p:OnTab s X)(v:OnTab s Y) :OnTab s (X*Y):=by
 obtain ⟨B,x,p⟩:=p; obtain ⟨C,h,v⟩:=v
 exact ⟨B*C,mul_nonneg x h,(p.and v).mono fun i h j=>(norm_mul_le ..).trans (mul_le_mul (h.1 j) (h.2 j) (norm_nonneg _) x)⟩
lemma UpTo.prod (A B:ℝ)(ha:0≤A)(hb:0≤B)(p:AllBills b s X A)(v:AllBills b s U B)(u:UpTo s X Y r)(e:UpTo s Z U q)(h:0≤r) : UpTo s (X*Z) (Y*U) (A*q+r*B):=by
 filter_upwards [u,e,p,v] with i u e p v j
 change dist (X i j * Z i j) (Y i j* U i j) ≤ _; rw [dist_eq_norm]
 rw [show X i j* Z i j-Y i j*U i j=X i j*(Z i j-U i j)+(X i j-Y i j)*U i j from (by rw [mul_sub,sub_mul]; abel)]
 exact (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (p j) ((dist_eq_norm (Z i j) (U i j)) ▸ e j) (norm_nonneg _) ha)) ((norm_mul_le ..).trans (mul_le_mul ((dist_eq_norm (X i j) (Y i j)) ▸ u j) (v j) (norm_nonneg _) h)))
lemma Agrees.prod (p:Agrees s X Y)(v:Agrees s Z U)(u:OnTab s X)(k:OnTab s Z) : Agrees s (X*Z) (Y*U):=by
 obtain ⟨B,h,u⟩:=u; obtain ⟨C,z,k⟩:= k.rotate v
 intro r t; let d:=r/(B+C+1); have he:0<d:=by unfold d; positivity
 have hp: d*(B+C+1)=r:=div_mul_cancel₀ _ (by positivity)
 exact ((p d he).prod B C h z u k (v d he) he.le).mono' (by linarith)
lemma OnTab.list (L:List I)(h:∀ i:ι,‖(1:b i)‖ ≤ 1)(X:I→ J→∀ i,b i) (p:∀ i∈ L,OnTab s (X i)) : OnTab s (fun j i=> (L.map fun k=> X k j i).prod) := by
 induction L with
 | nil=> exact OnTab.itself h
 | cons i l ih=> simp only [List.map_cons,List.prod_cons]; exact (p i (List.Mem.head ..)).prod (ih fun i h=>p i (List.Mem.tail _ h))
lemma Agrees.word (L:List I)(h:∀ i:ι,‖(1:b i)‖ ≤ 1)(X Y:I→ J→∀ i,b i) (p:∀ i∈ L,OnTab s (X i))(t:∀ i∈ L,Agrees s (X i) (Y i)) : Agrees s (fun j i=> (L.map fun k=> X k j i).prod) (fun j i=> (L.map fun k=> Y k j i).prod) := by
 induction L with
 | nil=> exact Agrees.refl _
 | cons i l ih=>
    let q (i:I)(u:i∈ l):=p i (List.Mem.tail _ u); simp only [List.map_cons,List.prod_cons]
    exact (t i (List.Mem.head ..)).prod (ih q fun i h=>t i (List.Mem.tail _ h)) (p i (List.Mem.head ..)) (OnTab.list l h X q)
-- common tolerance. require Approx Xj with shifted indices replaced by constant; yes use estimate statement with UpTo ≤ e for all unit-ahead. Don't demand Agrees before ε passed through outer estimate.
lemma power_list (L:List I)(h:∀ i:ι,‖(1:b i)‖≤1)(C:ℝ)(p:0≤C)(X:I→J→∀ i,b i)(u:∀ i∈ L,AllBills b s (X i) C) : AllBills b s (fun j i=> (L.map fun k=> X k j i).prod) (C^L.length):=by
 induction L with
 | nil=> simpa only [List.length_nil,List.map_nil,List.prod_nil,pow_zero] using (show AllBills b s (fun (_:J) (j:ι)=>(1:b j)) 1 from Eventually.of_forall (fun i=>h))
 | cons i l ih=>
    simp only [List.length_cons,List.map_cons,List.prod_cons,pow_succ']; exact ((u i (List.Mem.head ..)).and (ih fun i h=>u i (List.Mem.tail _ h))).mono fun j h i=> (norm_mul_le ..).trans (mul_le_mul (h.1 i) (h.2 i) (norm_nonneg _) p)
lemma limit_ticket (L:List I)(h:∀ i:ι,‖(1:b i)‖≤1)(C:ℝ)(p:0≤C)(r:ℝ)(u:0<r) : ∃ t:ℝ,0<t ∧ ∀ (X Y:I→J→∀ i,b i), (∀ i∈ L,AllBills b s (X i) C) → (∀ i∈ L,UpTo s (X i) (Y i) t)→ UpTo s (fun j i=> (L.map fun k=> X k j i).prod) (fun j i=>(L.map fun k=> Y k j i).prod) r :=by
 induction L generalizing r with
 | nil=> exact ⟨1,zero_lt_one,fun X Y _ _=> Eventually.of_forall fun i₁ i=>by simp only [List.map_nil,List.prod_nil, dist_self]; exact u.le⟩
 | cons i l ih=>
    let B:=C^l.length
    have hb:0≤B:=pow_nonneg p _
    let k:=r/(C+(B+r)+1); have hk:0<k:=by unfold k; positivity
    have hl:k≤r:= div_le_self u.le (by linarith)
    obtain ⟨q,z,qh⟩:= ih k hk
    refine ⟨min k q,lt_min hk z,fun X Y v a=>?_⟩
    let X'(j:J)(w:ι):=(l.map fun k=> X k j w).prod
    have hx (k:I)(d:k∈l):= v k (List.Mem.tail _ d)
    have x:AllBills b s X' B:= power_list l h C p X hx
    let Y'(j:J)(w:ι):=(l.map fun k=>Y k j w).prod; have hu: UpTo s X' Y' k:=qh X Y hx fun i h=>(a i (List.Mem.tail _ h)).mono' (min_le_right ..); have hv: AllBills b s Y' (B+r):= (x.and hu).mono fun i h j=>(norm_le_norm_sub_add (Y' i j) (X' i j)).trans (((add_le_add ((norm_sub_rev ..).le.trans ((dist_eq_norm (X' i j) (Y' i j)).ge.trans (h.2 j))) (h.1 j)).trans (by linarith)))
    have hp:k*(C+(B+r)+1)=r:=div_mul_cancel₀ _ (by positivity)
    simp only [List.map_cons,List.prod_cons]; exact (((a i (List.Mem.head ..)).mono' (min_le_left k q)).prod C (B+r) p (add_nonneg hb u.le) (v i (List.Mem.head ..)) hv hu hk.le).mono' (by linarith) -- tune dot UpTo.prod order. Need tolerance independent of X! change later.
end products

section tickets
open OS.Semigroup
variable {H:ι→Hilbert}{a:Axis}(S:∀ i,OS.Semigroup (H i) a)
variable {s:Filter J}{A B:J→∀ i,(H i).Op}
lemma OnTab.keeps1 (u:J→ℝ≥0) : OnTab s (fun j i=> (S i).E (u j)):= ⟨1,zero_le_one, Eventually.of_forall fun j i=>(S i).shrinks _⟩
lemma heat_toll (i:ι)(r' t u: ℝ≥0)(h:0<r')(p:r' ≤ t)(v:t≤u) : ‖(S i).E u-(S i).E t‖≤2* dist (u:ℝ) (t:ℝ) / (r':ℝ):=by
 let f:= (S i).E
 have T:=Plate.drift (S i) t (u-t) (h.trans_le p)
 have hu:‖f u-f t‖ ≤ 2*((u-t:ℝ≥0):ℝ)/(t:ℝ):= by
    rw [add_tsub_cancel_of_le v, (S i).roots_heat (lt_of_lt_of_le h (p.trans v)), (S i).roots_heat (h.trans_le p)] at T; exact T -- `rw at T` if let
 rw [Real.dist_eq,abs_of_nonneg (show 0≤(u:ℝ)-(t:ℝ) from sub_nonneg.mpr v)]; refine hu.trans ?_; rw [NNReal.coe_sub v]; exact div_le_div_of_nonneg_left (by exact mul_nonneg zero_le_two (sub_nonneg.mpr (show (t:ℝ) ≤ (u:ℝ) from v))) h p -- p typed
lemma heat_due' (i:ι)(r' t u: ℝ≥0)(h:0<r')(p:r' ≤ t)(v:r' ≤ u): dist ((S i).E u) ((S i).E t) ≤ 2*dist (u:ℝ) (t:ℝ) / (r':ℝ):=by rcases le_total u t with hu|hu; rw [dist_comm ((S i).E u),dist_eq_norm,dist_comm (u:ℝ)]; exact heat_toll S i r' u t h v hu; rw [dist_eq_norm]; exact heat_toll S i r' t u h p hu
lemma same_heat {t:J→ℝ≥0}{u:ℝ≥0} (v:0<u)(p:Tendsto t s (𝓝 u)): Agrees s (fun j i=>(S i).E (t j)) (fun _ i=>(S i).E u):=by
 intro r h; let a':=u/2; have ht:0<a':=half_pos v; have he:a'<u:=half_lt_self v
 have hp:Tendsto (fun i=> 2*dist (↑(t i):ℝ) (u:ℝ)/(a':ℝ)) s (𝓝 0):= by
    simpa only [dist_self,mul_zero,zero_div] using ((((NNReal.tendsto_coe.mpr p).dist (tendsto_const_nhds (x:=(u:ℝ)))).const_mul 2).div_const (a':ℝ))
 filter_upwards [hp.eventually (ge_mem_nhds h),p.eventually (le_mem_nhds he)] with j x y i; exact (heat_due' S i a' u (t j) ht he.le y).trans x
omit S
lemma UpTo.verify (Ω:∀ i,(H i).space)(h:∀ i,‖Ω i‖=1) {q:ℝ}(e:UpTo s A B q) : UpTo (b:=fun _ : ι=> ℂ) s (fun j i=> inner ℂ (Ω i) (A j i (Ω i))) (fun j i=> inner ℂ (Ω i) (B j i (Ω i))) q:=by
 filter_upwards [e] with j e i
 rw [dist_eq_norm, ←inner_sub_right,←ContinuousLinearMap.sub_apply]; have ht:= norm_inner_le_norm (𝕜:=ℂ) (Ω i) ((A j i-B j i) (Ω i)); have hx:= (A j i-B j i).le_opNorm (Ω i); rw [h i,one_mul] at ht; rw [h i,mul_one] at hx; exact ht.trans (hx.trans ((dist_eq_norm (A j i) (B j i)) ▸ e i))
lemma Agrees.verify (Ω:∀ i,(H i).space)(h:∀ i,‖Ω i‖=1) (e:Agrees s A B) : Agrees (b:=fun _ : ι=> ℂ) s (fun j i=> inner ℂ (Ω i) (A j i (Ω i))) (fun j i=> inner ℂ (Ω i) (B j i (Ω i))) := fun q u=> (e q u).verify Ω h
end tickets
end YM.SatinRegistration
open YM.SatinRegistration
#print axioms OnTab.later
#print axioms Agrees.word
#print axioms Agrees.scaled
#print axioms UpTo.prod
#print axioms limit_ticket
#print axioms same_heat
#print axioms Agrees.verify
