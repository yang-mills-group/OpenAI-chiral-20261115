import YM.CF.Brace.Hay
/-! Gauge and continuous exact bridge. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}{j l b n:ℕ}{e p d a w:ℝ}{X Y:Sheen m B}{U: Skin m B}{s:ArrayF m}{r:Zone}
lemma mantle_g (U:Skin m B)(x:Sheen m B)(v:Cue m)(g: Site (Domain m B)→E):mantle m B (gauge g U) (feast g x) (partner m B g v) ↔ mantle m B U x v:=by
 unfold mantle; rw [show tailP m B (feast g x) (partner _ _ g v)=onF g (tailP m B x v) by funext i; by_cases h:i.2=1 <;> simp [tailP,onF,capRow,arrayZ,feast,partner,h],ward_g]
lemma roof_glow(g: Site (Domain m B)→E)(U:Skin m B)(s:ArrayF m)(x:Sheen m B)(t:ℝ)(q:Sq)(i):roofV m B (gauge g U) (onF g s) (feast g x) t q i=turn (g i) (roofV m B U s x t q i):=by
 rw [roofV,roofV,show ∀ a b:Vect, turn (g i) (a+b)=turn (g i) a+turn (g i) b from fun i j=>map_add _ i j,turn_mul,turn_mul]
 congr 2; rw [paint,paint,turn_sum]; refine sum_congr rfl ?_; intro a h; rw [onF,freight_g,turn_mul]
lemma foe_g(g: Site (Domain m B)→E)(h:Foil m B e p r s X U): Foil m B e p r (onF g s) (feast g X) (gauge g U):=by
 refine ⟨(ward_g m B U s _ g).mpr h.flag,fun i=>?_,h.guard.cov _,slow_g _ _ g h.slowX,h.nonzero⟩
 simp [onF,feast,h.tags i]
variable (H:CoinG j l b n d a w)(G:Guide B e p d)(hm:b≤ (CSide m B).val)(M:Tulip.Male)
include H G hm
lemma hop_r(g: Site (Domain m B)→E)(h:Foil m B e p r s X U){w:Sq}(p:w∈zone r){u:ℝ}(k:u∈Set.Icc 0 1):ark m B (gauge g U) (onF g s) (feast g X) u w=feast g (ark m B U s X u w):=by
 funext i; apply Subtype.ext; change hook _ i=turn (g i) (hook _ i); rw [ark_u (foe_g g h) G w p u k,ark_u h G w p u k,turn_ren,roof_glow]
lemma torque_g (g: Site (Domain m B)→E)(h:Foil m B e p r s X U){v:Sq}(hv:v∈zone r): torque j l n M m B (gauge g U) (onF g s) (feast g X) v=torque j l n M m B U s X v:=by
 apply sum_congr rfl; intro i hi; have he:=mem_range.mp hi; have hx:= railIn n i he; have ht:=ber_m n (Nat.le_add_right i 1)
 rw [facePay,facePay,hop_r H G hm g h hv (hx ⟨le_rfl,ht⟩),hop_r H G hm g h hv (hx ⟨ht,le_rfl⟩), step_g H.stock H.posT hm g U _ _ (rail_g H G h hv i he)] -- binder order
lemma antler_g {z:Cue m}(g:Site (Domain m B)→E)(h:Guard U e)(hp:Slow U (hook X) p)(p:mantle m B U X z) : antler j l n M m B (gauge g U) (feast g X) (partner m B g z)= antler j l n M m B U X z:=by
 unfold antler; rw [show tailP m B (feast g X) (partner _ _ g z)=onF g (tailP m B X z) by funext i; by_cases h:i.2=1 <;> simp [tailP,onF,capRow,arrayZ,feast,partner,h]]; exact torque_g H G hm M _ (att_dome p h hp) (stick_in _ (mem_singleton_self 1))
lemma lick_g(g: Site (Domain m B)→E)(h:Guard U e)(hp:Slow U (hook X) p)(hy:Slow U (hook Y) p): lick j l n M m B (gauge g U) (feast g X) (feast g Y)=lick j l n M m B U X Y:=by
 obtain ⟨z,t,v⟩:= gets m B U X Y
 have he:tiedC m B (gauge g U) (feast g X) (feast g Y) (partner m B g z):=⟨(mantle_g ..).mpr t,(mantle_g ..).mpr v⟩
 have hX:Slow (gauge g U) (hook (feast g X)) p:=slow_g _ _ g hp; have hY: Slow (gauge g U) (hook (feast g Y)) p:=slow_g _ _ g hy
 rw [priceHero H G hm (h.cov g) hX hY he,priceHero H G hm (t:=z) h hp hy ⟨t,v⟩,hero,hero,antler_g H G hm M g h hp t,antler_g H G hm M g h hy v]
lemma tart_c:ContinuousOn (fun x: Skin m B × Sheen m B × Cue m=> antler j l n M m B x.1 x.2.1 x.2.2) {x|Guard x.1 e∧Slow x.1 (hook x.2.1) p∧mantle m B x.1 x.2.1 x.2.2}:=by
 let F(x:Skin m B×Sheen m B×Cue m):=tailP m B x.2.1 x.2.2
 have hf : Continuous F:=by apply continuous_pi; intro i; simp only [F,tailP,arrayZ,capRow]; split<;>fun_prop
 let T (x:Skin m B×Sheen m B×Cue m):hip m B:=(x.1,F x,x.2.1,stick 1)
 refine (flower (r:={1}) H G hm M).comp (f:=T) (show Continuous T from continuous_fst.prodMk (hf.prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const))).continuousOn (fun x h=>?_) -- tune
 change Guard x.1 _∧ _∧_ at h; exact ⟨att_dome h.2.2 h.1 h.2.1,stick_in _ (mem_singleton_self _)⟩
def reefU (m B:Side)(e p:ℝ): Set (Skin m B × Sheen m B × Sheen m B):={x| Guard x.1 e∧ Slow x.1 (hook x.2.1) p ∧ Slow x.1 (hook x.2.2) p}
omit G H hm in
lemma windowsT {X Y: Type*}[TopologicalSpace X][TopologicalSpace Y] (f : Y→ℂ)(t:X→ℂ) (F G : X→Y) (A : Set Y)(J:Set X) (x : X) (hf : ContinuousOn f A) (h₁ : Continuous F) (h₂ : Continuous G) (he : F x∈A) (hu : G x∈A) (H : x∈J)
    (hs : ∀ᶠ u in nhdsWithin x J, F u∈A) (ht : ∀ᶠ u in nhdsWithin x J, G u∈A) (hg : ∀ u∈J, F u∈A → G u∈A → t u=f (F u)-f (G u)) :
    ContinuousWithinAt t J x := by
  let v := (f ∘ F)-(f ∘ G)
  have hF : ContinuousWithinAt (f ∘ F) J x := Tendsto.comp (hf _ he) (tendsto_nhdsWithin_iff.mpr ⟨h₁.continuousAt.continuousWithinAt,hs⟩)
  have hG : ContinuousWithinAt (f ∘ G) J x := Tendsto.comp (hf _ hu) (tendsto_nhdsWithin_iff.mpr ⟨h₂.continuousAt.continuousWithinAt,ht⟩)
  change Tendsto _ _ (𝓝 (t x)); rw [show t x=v x from hg _ H he hu]
  apply Tendsto.congr' _ (show ContinuousWithinAt v J x from hF.sub hG)
  filter_upwards [self_mem_nhdsWithin, hs, ht] with u hx hu hv; exact (hg _ hx hu hv).symm
omit G H hm in
lemma open_gate {X Y: Type*}[TopologicalSpace X][TopologicalSpace Y] (F:X→Y) (A : Set X)(D:Set Y) (x : X) (h : Continuous F) (e : IsOpen D) (g : F x ∈ D) : ∀ᶠ y in nhdsWithin x A, F y ∈ D := h.continuousAt.continuousWithinAt (e.mem_nhds g)
lemma lick_c : ContinuousOn (fun x:Skin m B×Sheen m B×Sheen m B=> lick j l n M m B x.1 x.2.1 x.2.2) (reefU m B e p):=by
  let Z := Skin m B × Sheen m B × Sheen m B; let W:= fun t:Skin m B × Sheen m B × Cue m=> antler j l n M m B t.1 t.2.1 t.2.2
  let v: Z→ℂ:=fun x=> lick j l n M m B x.1 x.2.1 x.2.2; let S:Set (Skin m B × Sheen m B × Cue m):= {x|Guard x.1 e ∧ Slow x.1 (hook x.2.1) p∧ mantle m B x.1 x.2.1 x.2.2}; let J:=reefU m B e p
  intro t h; obtain ⟨z,Hx⟩:=gets m B t.1 t.2.1 t.2.2
  let F := fun x:Z=>(x.1,x.2.1,z); let V := fun x:Z=>(x.1,x.2.2,z)
  have hf:Continuous F:=continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const); have hv: Continuous V:= continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk continuous_const)
  have hs:= open_gate F J _ t hf (mantle_o m B) (show F t∈{x:Skin m B × Sheen m B × Cue m|mantle m B x.1 x.2.1 x.2.2} from Hx.1); have he := open_gate V J _ t hv (mantle_o m B) (show V t∈{x:Skin m B × Sheen m B × Cue m|mantle m B x.1 x.2.1 x.2.2} from Hx.2)
  refine windowsT W v F V S J t (tart_c H G hm M) hf hv ⟨h.1,h.2.1,Hx.1⟩ ⟨h.1,h.2.2,Hx.2⟩ h ?_ ?_ (fun x hx hp hu=> priceHero H G hm (t:=z) hx.1 hx.2.1 hx.2.2 ⟨hp.2.2,hu.2.2⟩ M)
  · filter_upwards [self_mem_nhdsWithin,hs] with i p e; exact ⟨p.1,p.2.1,e⟩
  filter_upwards [self_mem_nhdsWithin,he] with i p k; exact ⟨p.1,p.2.2,k⟩
end YM.CF.Brace
