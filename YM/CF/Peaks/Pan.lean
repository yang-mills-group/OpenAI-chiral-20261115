import YM.CF.Peaks.Mural
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P:Side} (G:Ratio N P)
-- Bool true residence input fine look, false root at embedded output
abbrev parcel (u:Bool) (e:ℝ): Branch.Tag (tempo G e) := if u then temper G e else torch G e
abbrev Tax {ι:Type*} (L:Side)(A:∀ i:ι, ∀ {c f:Side}(G:Ratio c f), Coil c f→Op (Iota G))(u v: Bool) (d C : ℝ) (k:ℕ)(e:ℝ):=
    ∀ i {N P:Side}(G:Ratio N P),G.count=L → k≤N.val→Crown (badge _) (parcel G u e) (parcel G v e) d C (fun x=> A i G x.val)
-- Implicit Pi binder inference shaky
abbrev Script (ι:Type*):=∀ i:ι, ∀ {c f:Side} (G:Ratio c f), Coil c f→Op (Iota G)
def Save {ι:Type*}(L: Side)(u v:Bool)(A:Script ι):=∃ d C e :ℝ,0<d∧0<C ∧0<e∧ ∃ k:ℕ,Tax L A u v d C k e
lemma parcel_eq (u:Bool)(a b:ℝ): (parcel G u a).run=(parcel G u b).run:=by cases u <;> rfl
variable {L: Side}{u v t:Bool}{ι:Type*}{A B : Script ι}
lemma recorded {d C e:ℝ}{k:ℕ}(h:Tax L @A u v d C k e)(p:0<d)(q:0<e): Save L u v @A:=⟨d,max 1 C,e,p,lt_max_of_lt_left zero_lt_one,q,k,fun i _ _ G he hg=> (h i G he hg).books (le_max_right ..)⟩
lemma decayV {a c δ e:ℝ}{k:ℕ}(p:Tax L @A u v a c k δ)(h:0<e)(g:e≤δ) : Tax L @A u v a c k e:=by
  intro i N P G he hg; let f:legal G e→legal G δ:= fun x=>⟨x.val,insideP G x.property g⟩
  have hx: Towards (tempo G δ) (badge _) (tempo G e) (badge _) f 1:=by
    refine ⟨continuous_subtype_val.subtype_mk _,rfl,rfl,fun _ _=>rfl,fun S x y=> ?_,fun b hV K HK γ q=> hV K HK (f ∘ γ) q⟩
    rw [one_mul]; change deal G S x.val y.val/|δ|≤ deal G S x.val y.val/|e|
    rw [abs_of_pos h,abs_of_pos (h.trans_le g)]; exact div_le_div_of_nonneg_left (deal_pos ..) h g
  exact hx.bring (parcel_eq ..) (parcel_eq ..) (p i G he hg) le_rfl
namespace Save
lemma pair {v' u':Bool}(p: Save L u v @A)(q: Save L u' v' @B): ∃ d K e:ℝ,0<d∧0<K∧0<e∧∃ k:ℕ,Tax L @A u v d K k e∧Tax L @B u' v' d K k e:=by
  obtain ⟨a,C,e,h,hc,hp,v,H⟩:=p; obtain ⟨d,P,f,p,pC,pe,w,S⟩:=q; let b:=lt_min hp pe
  refine ⟨min a d,C+P,min e f,lt_min h p,add_pos hc pC,b,max v w,fun i _ _ G hx hv=>?_,fun i _ _ G hx hv=>?_⟩
  · exact ((decayV H b (min_le_left e f) _ G hx ((le_max_left ..).trans hv)).drop (min_le_left ..)).books (by linarith)
  exact ((decayV S b (min_le_right e f) _ G hx ((le_max_right ..).trans hv)).drop (min_le_right ..)).books (by linarith)
lemma mul (p: Save L u v @A)(q: Save L v t @B): Save L u t (fun i _ _ G x=> A i G x*B i G x):=by
  obtain ⟨d,K,e,h,hP,hx,v,H,V⟩:= p.pair q; exact recorded (k:=v) (fun i _ _ G hg he=> (H i G hg he).product (V i G hg he) h.le) h hx
lemma plus (p: Save L u v @A)(q: Save L u v @B): Save L u v (fun i _ _ G x=> A i G x+B i G x):=by
  obtain ⟨d,K,e,h,hP,hx,v,H,V⟩:= p.pair q; exact recorded (k:=v) (fun i _ _ G hg he=> (H i G hg he).plus (V i G hg he)) h hx
lemma sub (p: Save L u v @A)(q: Save L u v @B): Save L u v (fun i _ _ G x=> A i G x-B i G x):=by
  obtain ⟨d,K,e,h,hP,hx,v,H,V⟩:= p.pair q; exact recorded (k:=v) (fun i _ _ G hg he=> (H i G hg he).sub (V i G hg he)) h hx
lemma one (ι:Type*): Save L u u (fun (_:ι) _ _ _ _=>1):=recorded (k:=0) (fun i _ _ G h k=> Crown.ident ..) (show 0<(1:ℝ) by norm_num) (show 0<(1:ℝ) by norm_num)
end Save
lemma curve {a c :ℝ}{k:ℕ}{e:ℝ}(p:Tax L @A u v a c k e)(H:0<a)(C:0<c)(he:0<e)(r:ℝ)(hp:0<r)(hz:∀ i {N P:Side}(G:Ratio N P),G.count=L→k ≤ N.val →A i G 1=0): ∃ b m:ℝ,0<b∧0<m∧m≤e ∧∃ v':ℕ, Tax L @A u v b r v' m:=by
  have hc:0≤quota:=le_trans (by norm_num:(0:ℝ)≤16) quota_bound
  obtain ⟨w,y,d,hy,hg,hd,hx,hB⟩:= clips C.le H hc hp
  let S:= bushpr (w+w) L.val 1
  have hS:1≤S:=by
    have hm:1≤ ((((w+w:ℕ):ℝ))+1)^4:=one_le_pow₀ (by simp)
    have hz:0≤(1+(L.val:ℝ))*priceF (w+w+L.val) 1:=by unfold priceF; positivity
    unfold S bushpr windowC; nlinarith
  let m:= e*y/S; have hj:0<m:=div_pos (mul_pos he hy) (zero_lt_one.trans_le hS)
  have hl:m≤y*e:= by rw [show m=e*y/S from rfl, mul_comm y]; exact div_le_self (by positivity) hS
  have hf:m≤e:=hl.trans (mul_le_of_le_one_left he.le hg.le)
  refine ⟨d,m,hd,hj,hf,k+2*(w+w+L.val)+3,fun i N P G hu hw=>?_⟩
  have hk:k≤ N.val := by omega
  let f: legal G m → legal G e:= fun z=> ⟨z.val,insideP G z.property hf⟩
  have ht:Towards (tempo G e) (badge _) (tempo G m) (badge _) f y:=by
    refine ⟨continuous_subtype_val.subtype_mk _,rfl,rfl,fun _ _=>rfl,fun P x z=>?_,fun b H K HK γ q=>H K HK (f ∘ γ) q⟩
    let W:= deal G P x.val z.val; change W/|e| ≤ y*(W/|m|); rw [abs_of_pos he,abs_of_pos hj]; apply (div_le_iff₀ he).mpr
    calc W=W/m*m:=by field_simp
         _ ≤ W/m*(y*e):=mul_le_mul_of_nonneg_left hl (div_nonneg (deal_pos ..) hj.le)
         _ = _:=by ring
  let X:legal G e:= ⟨1,crests G e he⟩
  have hw': 2*(w+w+G.count.val)+2<(More P).val:=by
    have hh:=G.exact_size; have he:N.val≤P.val:=by rw [hh]; exact Nat.le_mul_of_pos_right _ G.count.property
    rw [hu]; change _<P.val*2; omega
  refine ht.smaller (s':=parcel G u m) (t':=parcel G v m) (A:=fun x : legal G e=>A i G x.val) (p i G hu hk) w hg.le hd hx (temper_cap ..) hc (parcel_eq ..) (parcel_eq ..) X (hz i G hu hk) hy.le ?_ ?_
  · intro x o
    let Y:=(tempo G e).home o
    obtain ⟨g,hg⟩:=border G m hj x.val x.property (w+w) Y hw'
    use g; change deal G (bay (terr _) Y _) (jazz G g x.val) 1 /|e|≤y
    rw [abs_of_pos he]; apply (div_le_iff₀ he).mpr; apply hg.trans; rw [hu,show bushpr (w+w) L.val m=S*m by unfold S bushpr priceF; ring]; unfold m; field_simp; simp -- tune
  · simpa only [abs_of_pos hy,two_mul] using hB
end YM.CF.Peaks
