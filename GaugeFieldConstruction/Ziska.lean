import GaugeFieldConstruction.Hops
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes Tenant
variable {K b c d r v e a:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=> CSide m B
open Fock.Celeb
variable {S:Stamp m B}
variable {F G: MSheet m B}
lemma fuseR (p:PutM K n e a c F)(h:HitM K n e a d S G)(g:0≤a): HitM K n e a (Ka.β_H n*d*c) S (fun i=> F i*G i):=by
 have he:= HitM.turn (h.turn.fuseM p.turn g); convert he using 1; funext i; rw [Matrix.transpose_mul]; rfl
lemma HitM.drop_B (h:HitM K n e a c S G)(p:v≤a):HitM K n e v c S G:=by obtain ⟨q,A,k,p',l⟩:=h; exact ⟨q,A,k,(sum_le_sum fun i (_:i∈(univ:Finset (Single Λ)))=> sum_le_sum fun j (_:j∈(univ:Finset (Single Λ)))=> sale_mono (fun S x y=> mul_le_mul_of_nonneg_right (rent_up p S) (k.positive ..)) i j).trans p',l⟩
lemma coins_h (p:0<a)(g:0≤c):0 ≤ tallβ a c:= mul_nonneg (tsum_nonneg fun i:ℕ=>by unfold quota; positivity) g
section
variable {L:Side}{j:ℕ}{ho: Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
open Brace Fock.Celeb
-- bills denote derivative pollen
abbrev CloseS (T:tangD Λ) (j:ℕ):Pantry m B→Op (Single Λ):= fun i=>dir_g (TopPX m B j i) (coefM T (TopPX m B j) i)
-- q minus correction Φ
abbrev Honor (P:Grasp Y B e)(T:tangD Λ): SheetT m B:=fun i=> Spire.zen (Sobiq (TopPX m B j i) (TopCX m B i) (coefM T (TopPX m B j) i) (coefM T (TopCX m B) i))-Spire.zen (coefG T (BillMood P m) i)
private lemma Blore {f g PD CD I: MSheet m B}{p d w v:ℝ}(h:HitM K n e a c S f) (l:HitM K n e a d S g)(B₀:PutM K n e a w PD)(C₀:PutM K n e a v CD)(W₀:PutM K n e a p I)(g':0≤ a):
 let Z : MSheet m B:=fun x=> body (PD x) (CapeD (PD x) (CD x) (f x) (g x))*I x
 let q:=Ka.β_H n; HitM K n e a (q*(q*(q*((q*(q*c*v+q*d*w)*w)+(q*(q*c*v)*w))*w)*w)*p) S Z :=by -- last term f*c *? $(P*C)*f -> using (PD*(CD*cc f)); write equality
 intro Z Y; let φ:MSheet m B:=fun x=>CapeD (PD x) (CD x) (f x) (g x); unfold Z
 have hv:HitM K n e a (Y*(Y*c*v+Y*d*w)*w+ Y*(Y*c*v)*w) S φ := by
    have he: (Y*c*v+Y*d*w)=(Y*c*v+Y*d*w):=rfl -- reorder
    have hz:= ( ( (h.fuseM C₀ g').plus (fuseR B₀ l g')).fuseM (B₀.ccW) g').plus (fuseR B₀ (fuseR C₀ h.ccW g') g')
    convert hz using 1; funext x; unfold φ CapeD; simp only [Pi.add_apply,mul_assoc]
 exact ((fuseR B₀ hv g').fuseM (B₀.ccW) g').fuseM W₀ g'
-- Pre.Run.
lemma pollen (P:Grasp Y B e)(W:Pearl P)(w:Stamped j L ho Y)(hv:1≤j)(κ:ℝ):∃ a c0 c1:ℝ,0<a∧0≤c0∧0≤c1 ∧∀ {m:Side},P.roundZ≤(CSide m B).val→∀ (T:tangD (CSide m B)),‖T‖≤1 →
 (∀ x∈Lobby m B e,let ψ:= changeM P x.1 firstM; HasDerivAt (fun i:ℝ=>changeM P (bud T x.1 i) firstM) (acts (dg (CloseS (m:=m) (B:=B) T j x)) ψ + Honor P T x • ψ) 0)∧
 ∀ i:V8 (CSide m B), HookP i T→ HitM κ 6 e a c0 (Skye.ends i) (CloseS (B:=B) (m:=m) T j) ∧ Scribes κ 6 e a c1 (Skye.ends i) (Honor P T) :=by
 obtain ⟨K,hK,k⟩:= Chaff.larder 7; let p:= max (max (lin_T 7*K*κ) κ) K; have hx:K≤p:=le_max_right ..; have hp: hud_T 7 K:=k; have hu:κ≤p:=(le_max_right ..).trans (le_max_left ..); have hh:1 ≤ p:=hK.trans hx; have hc:lin_T 7*K*κ ≤ p:=(le_max_left ..).trans (le_max_left ..)
 obtain ⟨a,d,e',v,hA,h₀,h₁,h₂,q⟩:= clusterV P hh
 let A:=min (a/2) (rateMo B (radF P)); have he:0<A:=lt_min (half_pos hA) (div_pos (Jet.rad_pos P) (by unfold Dial.feeG; positivity))
 have hy:A≤a/2:=min_le_left ..
 obtain ⟨F,l,H⟩:=bishop P p hh hp hx hc
 let X:=tallβ a d; let Q:=tallβ a e'; let P':=Ka.β_H 6; let G:=P'*(P'*(P'*((P'*(P'*X*e'+P'*Q*d)*d)+(P'*(P'*X*e')*d))*d)*d)*v
 let L:ℂ→L[ℝ]ℂ:= zcl.comp (((2:ℂ)⁻¹) • ContinuousLinearMap.id ℝ ℂ)
 have ha: 0≤ G:=by
   have hv:0 ≤ X:=coins_h hA h₀; have he:0 ≤Q:=coins_h hA h₁; have hz:0 ≤ P':=by unfold P' Ka.β_H; positivity
   unfold G; positivity
 refine ⟨A,P'*X*d+P'*X*d, ‖L‖*G+‖zcl‖*F,he,?_ ,by positivity,@fun m u T t=>?_⟩
 · have ht:0 ≤ P':=by unfold P' Ka.β_H; positivity
   have hv:0 ≤ X:=coins_h hA h₀
   positivity
 obtain ⟨h,g,q⟩:= q m u
 obtain ⟨hq,H⟩:=H m u T t; let V:=TopPX m B j; let Z:=TopCX m B
 constructor
 · intro i y ψ
   let Bv:= bud T i.1; let R(t:ℝ):= (Bv t,i.2)
   have e₀:Bv 0=i.1:=bud_x ..
   have he:Continuous R:= ((bud_c T).comp (f:=fun x:ℝ=>(x,i.1)) (continuous_id.prodMk continuous_const)).prodMk continuous_const
   have ht:∀ᶠ t in 𝓝 (0:ℝ), R t∈Lobby m B e:=he.continuousAt.eventually (lobby_o.mem_nhds (by unfold R; rw [e₀]; exact y)) -- e shadow preparation ambig
   have he:= motionK W w u hv 0 Bv (fun _=>i.2) (f:=coefM T V i) (B':=coefM T Z i) (φ:=coefG T (BillMood P m) i) (PutM.pair_V T t h hp hx i y) (PutM.pair_V T t g hp hx i y) (hq i y) (ht.mono fun _ p=>(lobby_G p).1) (ht.mono fun _ p=>(lobby_G p).2)
   rw [e₀] at he; exact he
 intro i hT
 let Sf:=TopPX m B j; let Gf:=TopCX m B; let f:=coefM T Sf; let g':=coefM T Gf; let Y:=ends i; have hP:PutM κ 6 e A d Sf:= lower_h h hu (by decide) (hy.trans (half_le_self hA.le)); have hz:= HitM.drop_B (offshore i T t h hp hx hc hT hA) hy; have hk:= HitM.drop_B (offshore i T t g hp hx hc hT hA) hy; have he':HitM κ 6 e A _ Y (fun x=>body (Sf x) (CapeD (Sf x) (Gf x) (f x) (g' x))*TopIX m B j x):=Blore hz hk hP (lower_h g hu (by decide) (hy.trans (half_le_self hA.le))) (lower_h q hu (by decide) (hy.trans (half_le_self hA.le))) he.le
 refine ⟨?_,?_⟩
 · have h:= (hz.fuseM hP he.le).plus (fuseR hP hz he.le|>.negW); convert h using 1; funext x; unfold CloseS dir_g; simp only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg]; rfl
 let U:= Scribes.traceH _ he'; have m:= (U.lin_B L le_rfl).add_B (((H _ hT|>.down_B (min_le_right ..)).lin_B zcl le_rfl).neg_B); convert m using 1; funext i; unfold Honor; rw [sub_eq_add_neg]; congr 1; unfold Sobiq; rw [div_eq_mul_inv,mul_comm]; rfl
-- phase-element identification post.
end
end YM.CF.XGarden
end
