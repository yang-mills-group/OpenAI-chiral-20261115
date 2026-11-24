import YM.CF.Peaks.Lintel
import YM.CF.Drapes.Rig
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{u v:Bool}{L:Side}{A B : Script ι}
def Score (L: Side)(A: Script ι)(u v:Bool)(d r:ℝ)(m k:ℕ)(e:ℝ):= ∀ i {N P:Side}(G:Ratio N P),G.count=L→ k ≤ N.val → Street (badge (legal G e)) (parcel G u e) (parcel G v e) m (L.val:ℝ)⁻¹ d (fun _=>r) (fun x=> A i G x.val)
lemma weighted {a c :ℝ}{k:ℕ}{e:ℝ}(p:Tax L @A u v a c k e)(H:0<a)(C:0<c)(he:0<e)(r:ℝ)(hp:0<r)(hz:∀ i {N P:Side}(G:Ratio N P),G.count=L→k ≤ N.val →A i G 1=0)(u1:ℕ) : ∃ b m:ℝ,0<b∧0<m∧m≤e ∧∃ v':ℕ, Score L @A u v b r u1 v' m:=by
  have hc:0<quota:=lt_of_lt_of_le (by norm_num:(0:ℝ)<16) quota_bound
  obtain ⟨w,y,d,hy,hg,hd,hq,hx,hB⟩:= gain C.le H hc hp u1
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
  let V:=quota*(((((w+w):ℕ):ℝ)+1)^4); let D:=Real.exp (-a/2*w)*c
  let z:= V*Real.exp (2*d*V)*(D+c*(2*y))+D
  have hW : Crown (badge _) (parcel G u m) (parcel G v m) (2*d) z ((fun (x:legal G e)=>A i G x.val) ∘ f):=by
    refine ht.smaller (s':=parcel G u m) (t':=parcel G v m) (A:=fun x : legal G e=>A i G x.val) (p i G hu hk) w hg.le (by positivity) hx (temper_cap ..) hc.le (parcel_eq ..) (parcel_eq ..) X (hz i G hu hk) hy.le ?_ ?_
    · intro x o
      let Y:=(tempo G e).home o
      obtain ⟨g,hg⟩:=border G m hj x.val x.property (w+w) Y hw'
      use g; change deal G (bay (terr _) Y _) (jazz G g x.val) 1 /|e|≤y
      rw [abs_of_pos he]; apply (div_le_iff₀ he).mpr; apply hg.trans; rw [hu,show bushpr (w+w) L.val m=S*m by unfold S bushpr priceF; ring]; unfold m; field_simp; simp -- tune
    · unfold z D V; simp only [abs_of_pos hy,two_mul,le_refl]
  have hp':0<(L.val:ℝ):=side_pos _
  exact (deck_adap hW hd hq le_rfl u1 ((L.val:ℝ)⁻¹) (by positivity) (by rw [inv_le_one₀ hp']; exact_mod_cast L.property)).prime (fun _=>hB)
end YM.CF.Peaks
