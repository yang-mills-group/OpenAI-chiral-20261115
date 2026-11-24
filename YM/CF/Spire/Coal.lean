import YM.CF.Spire.Hats
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Phase.Sample Broc Branch Jet MeasureTheory
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L A m B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P: Grasp Y B e}(K:Pearl P)(H:Stamped j L ho Y)(p:0<e)(q:1≤j)
lemma qtz(m:Side)(S:Broc.Table m B): cloudG (idrat (CSide m B)) S=S:=by ext; simp [cloudG,filed]
include K H p q
lemma album(n:ℕ)(c:ℝ)(w:1≤c):∃ k l:ℝ, 0<k∧ 0≤l∧∀ m:Side, P.roundZ≤(CSide m B).val →∀ M:Tulip.Male, let G:=idrat (CSide m B); Screen (dressL G e) (LineE n G c e) n (fun i=> candle m B (P.cost m M) i.val.2) k l:=by
 obtain ⟨v,D,W⟩:=star_cost n (zero_le_one.trans w) B; obtain ⟨C,h,V⟩:= mis_work P n v (w.trans D)
 let a:= radF P; let U:=feeG (8*B.val); have he:0<a:=rad_pos _; have ht:0<U:=by unfold U feeG; positivity
 obtain ⟨s,u,L⟩:=pureZ n c B w; obtain ⟨z,j,h'⟩:=stash s u n (div_pos he ht)
 refine ⟨a/U/2,z*(U*C),by positivity,by positivity,fun m g M=> ?_⟩
 let N:=CSide m B; intro G; let A:=bliss (e:=e) G
 let F:= fun x: Gift0 (e:=e) G=>candle m B (P.cost m M) x.val.1.val.2
 have hk(x: Gift0 (e:=e) G):ZeroF m B x.val.1.val.2 x.val.2:= law_rich _ _ _ _ x.property -- tune
 let f(x: Gift0 (e:=e) G): Brace.Chord m B e P.p:=⟨(x.val.1.val.2, hatchL G x),⟨x.val.1.property.cg,starK P.topB p.le x.val.1.property.cg (hk _)⟩⟩
 have hg:Continuous f:=by
   apply Continuous.subtype_mk
   have hv:Continuous (fun x: Gift0 (e:=e) G=>x.val.1.val.2):=continuous_snd.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
   let P' (x: Gift0 (e:=e) G):= (x.val.1.val.2, x.val.2); have ht:Continuous P':=hv.prodMk (continuous_snd.comp continuous_subtype_val)
   exact hv.prodMk ((starfish_c (m:=m) P.topB p.le).comp_continuous (f:=P') ht fun x=> ⟨x.val.1.property.cg,hk x⟩)
 have hx: Screen A.botL (SparY n G c e) n F (a/U) (U*C):=by
    let t:=fun i:↑(Brace.Chord m B e P.p)=> Spire.zen (hum m B (P.cost m M) i.val.1 i.val.2 - song m B (P.cost m M) i.val.1 i.val.2)
    have hf:F=t ∘ f:=funext fun x=> candleL K H g q _ x.val.1.property.cg M _ (fun i j=>(starK K.ample p.le x.val.1.property.cg (hk x) i j).trans_le K.wide)
    rw [hf]; apply Screen.leaps (Ω:=SparY n G c e) (Φ:=foam _ (8*B.val)) (b:=pWorks m B e P.p) (c:=A.botL) (v:=U) (w:=U) (V m g M) (foams _ (mul_pos (by decide) B.property) _) f hg h (div_nonneg he.le ht.le) (le_of_eq (div_mul_cancel₀ _ ht.ne')) ?_ ?_ ?_
    · intro S X Y t; have hv:=t.2; have hf:= t.1.2; unfold SupA at hv; rw [qtz] at hv hf
      exact ⟨fun i x y=> hf i (foam_in _ _ S x) (foam_in _ _ S y), honor _ _ S hv hf⟩
    · intro x y; refine ⟨scaleG G y,Subtype.ext ?_⟩; let S:=(scaleG G y); let P':=x.val.1.val; exact Prod.ext rfl (starG P.topB p.le x.val.1.property.cg (hk _) S)
    intro E _ _ _ T t g k x l; obtain ⟨_,z,F⟩:= k x l; exact ⟨fun i=> (z i).mono D, W _ m _ _ x z F _ _ p.le (g x).val.1.property.cg (hk _) P.topB⟩
 have hp (R:Broc.Table m B): (SupA G R).card ≤ R.card:= (rate_cap _).trans (cloud_count G R)
 letI:CompactSpace ↑(Rent0 G e):=open_tr ..
 have hR:= screen_mean A (L m m e G) hx hp (fun S x=> (complex_down m B (cloudG G S):Down _ _)) (fun S x y p=> trans_t G x y S p) (fun S x=> ⟨fun _ _ _=> rfl,fun _ _ _=>rfl⟩) j (fun T v p=> h' _ p _ _ (hp _))
 convert hR using 1; funext x; unfold means
 let Z:= opensD G e; let c:= candle m B (P.cost m M) x.val.2
 rw [show (∫ t, cream _ F (x,t) ∂ _)=∫ t, fall (Z x) t • c ∂ fares _ cloud from ?_,integral_smul_const,sails_all,one_smul]
 apply integral_congr_ae; apply Eventually.of_forall; intro t
 unfold cream; by_cases h:fall (Z x) t ≠ 0
 · dsimp only; rw [sampler_p F (x,t) h]
 rw [not_not] at h; change fall (Z x) t • _=fall (Z x) t • _; rw [h,zero_smul,zero_smul]
end YM.CF.Spire
