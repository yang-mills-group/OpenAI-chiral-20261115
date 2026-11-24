import GaugeFieldConstruction.VineΓ
set_option autoImplicit false
set_option maxHeartbeats 240000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
-- sum over stencil. unitaries factors. weights. arbitrary n0.
namespace Trackℓ
variable {N:Side}
lemma Foenix (k:ΛN) : ∃ S:Finset Book,∀ (x:Cover) (A:Chip),Berth x A→ σU x A k∈S:=by
 let Gw:=↥grabG; let Gf:=↥grabF; let F(x:Wφ)(b:Bool)(k:ℕ):=(tariff 1 k:ℂ) • boon (stride b) (pinF x) (Garn x) k
 let X(m:Gw × Gw):=σU 0 (.litt m.1.val m.2.val) k
 let Y(m:Gf × Gf):Book:=if k.2.2=0 then αF (F m.1.val false k.1) (F m.2.val true k.2.1) else 0
 let Z(m:Gf×Gf×Gw):Book:=αM (eG 0 m.2.2.val k.2.2) (F m.1.val false k.1) (F m.2.1.val true k.2.1)
 have he(x:Cover)(i:Wα)(m): eG x i m=eG 0 (zG x i) m:=by unfold eG; rw [G_near]; try rfl
 have hp(x:Cover)(i:Wφ)(b: Bool)(m):eF x i b m=F (zF x i) b m:=by unfold eF; rw [F_near]; try rfl
 refine ⟨univ.image X ∪ (univ.image Y∪univ.image Z),fun x a p=>?_⟩; cases a with
 | litt i j=>
    let u:Gw:= ⟨zG x i,p.1⟩; let v:Gw:=⟨zG x j,p.2⟩
    rw [show σU x (.litt i j) k=X (u,v) from by dsimp only [σU]; rw [he, he x j]; try rfl]; exact mem_union_left _ (mem_image_of_mem X (mem_univ _))
 | cuff i j=>
    let u:Gf:=⟨zF x i,p.1⟩; let v:Gf:=⟨zF x j,p.2⟩
    rw [show σU x (.cuff i j) k=Y (u,v) from by dsimp only [σU]; rw [hp,hp]] -- tune clear
    exact mem_union_right _ (mem_union_left _ (mem_image_of_mem Y (mem_univ _)))
 | creel g u v=>
    let G:Gw:=⟨zG x g,p.1⟩; let U:Gf:=⟨zF x u,p.2.1⟩; let V:Gf:= ⟨zF x v,p.2.2⟩
    rw [show σU x (.creel g u v) k=Z (U,V,G) from by dsimp only [σU]; rw [he,hp,hp]]
    exact mem_union_right _ (mem_union_right _ (mem_image_of_mem Z (mem_univ _)))
-- 'bounded' elementary
abbrev ChipBound (U:ℕ→ℂ) := ∃ c:ℝ,0≤c∧∀ᶠ i:ℕ in atTop, ‖U i‖≤ c
lemma C_funds (a b:ℕ→ℂ)(p:ChipBound a)(h:ChipBound b): ChipBound (fun i=>a i+b i):=by obtain ⟨c,x,u⟩:=p; obtain ⟨d,v,e⟩:=h; exact ⟨c+d,add_nonneg x v,(u.and e).mono fun i H=>(norm_add_le ..).trans (add_le_add H.1 H.2)⟩
lemma Lint_sum{X:Type*}(s:Finset X)(f:X→ℕ→ℂ)(h:∀ i∈s,ChipBound (f i)): ChipBound (fun i=>∑ j∈s,f j i):=by induction s using Finset.induction_on with|empty=> simp only [sum_empty]; exact ⟨0,le_rfl,Eventually.of_forall fun _=>by simp⟩|insert i t w ih=> simp_rw [sum_insert w]; exact C_funds _ _ (h i (mem_insert_self ..)) (ih fun i p=> h i (mem_insert_of_mem p))
variable (U:ℕ→Book→ₗ[ℂ]ℂ)(F:Book→ₗ[ℂ]ℂ)(H:∀ p:Book,Tendsto (fun i=>U i p) atTop (𝓝 (F p))){x:ℕ→Payν N}{P : Genre}{B : ℝ}(h: Wagon x P B)(p:300<N.val)
include H h p
lemma εTar (k:ΛN): ChipBound (fun i=>U i (sigΨ (x i) k)):=by
 obtain ⟨S,y⟩:= Foenix k; obtain ⟨K,v,L,u⟩:=couponL h p; let A:= 1+∑ i∈S, ‖F i‖; have he(z:Book)(e:z∈S):‖F z‖+1≤ A:=by refine (le_trans (add_le_add_left (single_le_sum (s:=S) (f:= fun i=> ‖F i‖) (fun i _=>norm_nonneg _) e) 1) ?_); unfold A; rw [add_comm]
 have ha:0≤A:=by unfold A; positivity
 refine ⟨↑K*(v*A),by positivity,?_⟩; have hp:∀ᶠ i:ℕ in atTop,∀ j∈S,‖U i j‖≤ A:= eventually_all_finset S|>.mpr (fun j p=> ((H j).norm.eventually (gt_mem_nhds (show ‖F j‖<A from lt_of_lt_of_le (lt_add_one _) (he _ p)))).mono fun i h=> le_of_lt (Set.mem_Iio.mp h)) -- name tune
 filter_upwards [hp] with i g; rw [sigΨ,map_sum]; apply le_trans (norm_sum_le ..); let t:=x i; refine le_trans (sum_le_sum (g:=fun _=>v*A) fun j _=>?_) ?_
 · rw [map_smul, norm_smul]; exact mul_le_mul ((u i).2 _) (g _ (y t.1 _ (Uptick (x i).1 N (x i).2.1 j))) (norm_nonneg _) L.le -- tune
 simp only [sum_const,card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast (u i).1) (mul_nonneg L.le ha)
lemma εRig (t j:ℕ):ChipBound (fun i=> U i (CrestJ t (x i) j)):=by simp_rw [CrestJ,map_sum]; exact Lint_sum _ _ (fun i _=>εTar _ F H h p i)
-- converge readings.Analytic use
omit H h p in
lemma L_ghost {A B:ℕ→ℂ}(h:Tendsto A atTop (𝓝 0))(v:ChipBound B): Tendsto (fun i=>A i*B i) atTop (𝓝 0):=by
 obtain ⟨c,a,p⟩:=v; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (g:=fun i=> ‖A i‖*c) (p.mono fun i h=>by rw [norm_mul]; gcongr) ?_ ; simpa using h.norm.mul_const c -- tune
lemma voyage (t:ℕ→ℝ)(w:Tendsto t atTop (𝓝 0))(l:∀ᶠ i:ℕ in atTop, 0<t i)(n e:ℕ)(d:e≤3*n)(v:Book)(z:∀ᶠ i:ℕ in atTop,(CrestJ n (x i) e=v) ∧∀ j<e,CrestJ n (x i) j=0) : Tendsto (fun i=> U i (((t i:ℂ)^e)⁻¹ • RankBook (t i) n (x i))) atTop (𝓝 (F v)):=by
 let Q(i j:ℕ):=((t i:ℂ)^e)⁻¹ * ((t i:ℂ)^j*U i (CrestJ n (x i) j)); have hp(j:ℕ): Tendsto (fun i=>Q i j) atTop (𝓝 (if j=e then F v else 0)):=by
    obtain p'|p'|p':= lt_trichotomy j e
    · rw [if_neg p'.ne]; apply tendsto_const_nhds.congr'; filter_upwards [z] with i h; simp [Q,h.2 j p']
    · subst j; rw [if_pos rfl]; apply (H v).congr'; filter_upwards [z,l] with i h p; have hp: (t i:ℂ)≠0:=ofReal_ne_zero.mpr p.ne'; simp [Q,h.1,hp]
    rw [if_neg p'.ne']; let r:=j-e; let T (i:ℕ):=(t i:ℂ)^r; have hr:r≠0:= Nat.ne_of_gt (Nat.sub_pos_of_lt p'); have he:Tendsto T atTop (𝓝 0):= by simpa [hr] using (continuous_ofReal.continuousAt.tendsto.comp w).pow r
    apply (_root_.Filter.Tendsto.congr' _ (L_ghost he (εRig U F H h p n j))) -- binder tune remove U,h included
    filter_upwards [l] with i h; let s:= (t i:ℂ); have he:s≠0:= ofReal_ne_zero.mpr h.ne'; have hs:s^j=s^e*s^r:=by rw [←pow_add]; congr; omega
    let V:=U i (CrestJ n (x i) j); change s^r*V=(s^e)⁻¹*(s^j*V); rw [hs, ←mul_assoc _ _ V]; field_simp
 rw [show F v=∑ j∈range (3*n+1),(if j=e then F v else 0) by simp [show e<3*n+1 by omega]]
 refine (tendsto_finsetSum _ (fun j _=> hp j)).congr (fun i=> ?_); rw [map_smul,prism_W, map_sum]; simp only [map_smul,smul_eq_mul,mul_sum]; try rfl
end Trackℓ
end YM.GaugeFieldConstruction.Wick.Yacht
end
