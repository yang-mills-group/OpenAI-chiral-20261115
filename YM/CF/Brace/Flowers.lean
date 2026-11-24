import YM.CF.Brace.Fencing
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B: Side}{j l b n:ℕ}{e p d a w:ℝ}{r:Zone}
variable (H:CoinG j l b n d a w)(G:Guide B e p d)
include H G
def TopArc (m B:Side)(e p:ℝ)(r:Zone) := {x:hip m B|Foil m B e p r x.2.1 x.2.2.1 x.1 ∧ x.2.2.2∈zone r}
variable(hm:b≤ (CSide m B).val)
include hm
lemma flower (M:Tulip.Male): ContinuousOn (fun x:hip m B=>torque j l n M m B x.1 x.2.1 x.2.2.1 x.2.2.2) (TopArc m B e p r):=by
  unfold torque; apply continuousOn_finsetSum; intro i hi; have ht:i<n:=mem_range.mp hi
  let S:=railIn n i ht; let f (t:ℝ)(x:hip m B):=ark m B x.1 x.2.1 x.2.2.1 t x.2.2.2
  let L(x:hip m B): Gaz (CSide m B):=(x.1,f (berth n i) x,f (berth n (i+1)) x); have he:B=B:=rfl
  have hg : ContinuousOn L (TopArc m B e p r):= by
    intro x hx; change Foil _ _ _ _ r x.2.1 x.2.2.1 x.1 ∧ _ at hx
    have hp : ContinuousAt L x:= continuous_fst.continuousAt.prodMk ((ark_at e p d (berth n i) r G x hx.1 hx.2 (S ⟨le_rfl,ber_m n (Nat.le_add_right ..)⟩)).prodMk (ark_at e p d (berth n (i+1)) r G x hx.1 hx.2 (S ⟨ber_m n (Nat.le_add_right ..),le_rfl⟩)))
    exact hp.continuousWithinAt
  let F:= fun t:Gaz (CSide m B)=>openC j l M t.1 t.2.1 t.2.2
  have hL: ContinuousOn F {x:Gaz (CSide m B)|Gaze x.1 x.2.1 x.2.2 d}:=pore_c (N:=CSide m B) H.stock H.posT hm M
  change ContinuousOn (F ∘ L) _
  apply hL.comp hg; intro x h; exact rail_g H G (show Foil _ _ _ _ r x.2.1 x.2.2.1 x.1 from h.1) (show x.2.2.2∈zone r from h.2) i ht
lemma buks(x y:Sheen m B)(t u:ArrayF m)(U:Skin m B)(M:Tulip.Male)(h: Foil m B e p r t x U)(k: Foil m B e p r u y U)(f:∀ i:Spot m,i.2∈r→ t i=u i)(q s:Sq)(hp:q∈zone r)(hs:s∈zone r): torque j l n M m B U t x q - torque j l n M m B U u y q=torque j l n M m B U t x s-torque j l n M m B U u y s:=by
  let R (A:ArrayF m)(B':Sheen m B)(w):=torque j l n M m B U A B' w
  have hv(v)(g:v∈zone r):airing _ _ U t v= airing _ _ U u v:=by
    rw [←rise_one _ _ U t v x,←rise_one _ _ U u v x]; exact ark_same m B U t u r f x 1 g
  have Hc(a)(v)(h:Foil m B e p r a v U): ContinuousOn (R a v) (zone r):=by
    let L:=fun p':Sq=>(U,a,v,p'); have hx:Continuous L:= continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    exact (flower (r:=r) H G hm M).comp (f:=L) hx.continuousOn (fun i p=>⟨h,p⟩)
  have he(v)(g:v∈zone r): Complex.exp (R t x v-R u y v) • coneP j M U x=coneP j M U y:=by
    obtain ⟨F,-⟩:=tor_ok H G hm h g M; obtain ⟨A,-⟩:=tor_ok H G hm k g M; unfold R
    rw [Complex.exp_sub,div_eq_inv_mul,mul_smul,F,hv v g,←A,smul_smul,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul]
  exact carry_log (cube_path r).isPreconnected continuousOn_const ((Hc t x h).sub (Hc u y k)) q hp (v:=fun _=>R t x q-R u y q) (fun z p=>smul_left_injective ℂ ((tor_ok H G hm h hp M).2) ((he q hp).trans (he z p).symm)) rfl s hs
omit H G hm
def arrayZ(m B:Side)(x:Sheen m B): ArrayF m:= fun i=>x (address m B i.1)
def tailP(m B:Side)(x:Sheen m B)(y:Cue m): ArrayF m:= capRow (arrayZ m B x) 1 y
def mantle(m B:Side)(U:Skin m B)(x:Sheen m B)(t:Cue m):=Attested m B U (tailP m B x t) (insert 1 {0})
def tiedC(m B:Side)(U:Skin m B)(x y:Sheen m B)(t:Cue m):=mantle m B U x t ∧ mantle m B U y t
lemma tiesT (m B:Side)(U:Skin m B){I:Type}[DecidableEq I]{S :Finset I}(h:S.card≤6)(f:I→Sheen m B): ∃ t,∀ i∈S,mantle m B U (f i) t:=Att_end m B U S (fun i=>arrayZ m B (f i)) (fun _=>{0}) 1 h (fun _ _=>by simp [ending]) (fun i _=>baseA m B U (arrayZ m B (f i)))
lemma gets(m B:Side)(U:Skin m B)(x y:Sheen m B):∃ t,tiedC m B U x y t:=by
 obtain ⟨z,h⟩:=tiesT m B U (show (univ:Finset Bool).card≤6 by simp) (fun i=> if i then x else y)
 exact ⟨z,h true (mem_univ _),h false (mem_univ _)⟩
lemma mantle_o(m B: Side): IsOpen {t: Skin m B×Sheen m B×Cue m | mantle m B t.1 t.2.1 t.2.2}:=by
 let F(x:Skin m B × Sheen m B × Cue m):ArrayF m:= tailP m B x.2.1 x.2.2
 have hf : Continuous F:=by apply continuous_pi; intro i; simp only [F,tailP,arrayZ,capRow]; split<;>fun_prop
 exact (ward_c _ _ _).preimage (continuous_fst.prodMk hf)
end YM.CF.Brace
