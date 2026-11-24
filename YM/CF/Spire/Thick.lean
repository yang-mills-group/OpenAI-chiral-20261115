import YM.CF.Spire.Coal
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Phase.Sample Broc Branch Jet MeasureTheory
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L A m B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P: Grasp Y B e}(K:Pearl P)(H:Stamped j L ho Y)(p:0<e)(q:1≤j)
abbrev CapX (m B:Side)(e:ℝ):= {x:Skin m B//Guard x e}
def soar (m B:Side)(e:ℝ):Light (Site (Domain m B)) (CapX m B e) (Funds m B) where
 frame:=terr _
 dress f x:=⟨gauge f x.val,x.property.cov f⟩
 rel S x y:= Agrees S x.val y.val
 expands S T h x y p:= fun i a b=>p i (h a) (h b)
def aether (n:ℕ)(K e:ℝ)(m B:Side):Draw (CapX m B e):=⟨fun E _ _ _ V f=>∀ x∈V,TransK n (fun y=> (f y).val) x K⟩
include p q H K
lemma cycle (n:ℕ)(z:ℝ)(k:1≤z):∃ a v:ℝ,0<a ∧0≤v∧∀ m:Side,P.roundZ ≤ (CSide m B).val→∀ M:Tulip.Male,Screen (soar m B e) (aether n z e m B) n (fun x=>candle m B (P.cost m M) x.val) a v:=by
 obtain ⟨c,v,h,u,W⟩:= album K H p q n z k; refine ⟨_,_,h,u,fun m g M=>?_⟩; let G:=idrat (CSide m B)
 let L(x:CapX m B e):Rent0 G e:=⟨(x.val,x.val),jointly x.val x.property p⟩
 have he:= (W m g M).leaps (Φ:=id) (c:=soar m B e) (Ω:=aether n z e m B) (q:=c) (v:=1) (w:=1) (idemX (terr _)) L ((continuous_subtype_val.prodMk continuous_subtype_val).subtype_mk _) u h.le (by simp) (fun S x y t=> by
    have ht:cloudG G S=S:=qtz m S; exact ⟨t,ht.symm ▸ t⟩) (fun x y=> by
    have he:scaleG G y=y:=by funext; simp only [G,scaleG,filed,Function.comp_apply]
    refine ⟨y,Subtype.ext ?_⟩; change (gauge y _,gauge y _)= (gauge y _,gauge (scaleG G y) _); rw [he]) (fun E _ _ _ V h f t x hx=> ⟨t x hx,t x hx⟩)
 rw [one_mul] at he; exact he
lemma coffer(n:ℕ)(z:ℝ)(k:1≤z):∃ a v:ℝ,0<a∧0<v∧∀ (m A:Side) (G:Ratio (CSide m B) (CSide A B)), G.count=L→P.roundZ≤ (CSide m B).val →∀ M:Tulip.Male, Screen (dressL G e) (LineE n G z e) n (fun i=> altar G P i.val M) a v:=by
 obtain ⟨a,v,h,t,F⟩:=cycle K H p q n z k; obtain ⟨c,w,hw,u,Q⟩:= conductor P p n z k; let A:= feeG L.val; have ht:0<A:=by unfold A feeG; positivity
 let w':= min (min a c) (a/A); have hu:0<w':=lt_min (lt_min h hw) (div_pos h ht)
 refine ⟨w', w+A*v+v,hu,by positivity,fun m r G h g M=>?_⟩
 let V:=fun x:Rent0 G e=> flakeL P G x.val M; have he: Screen (dressL G e) (LineE n G z e) n V w' w:= (Q _ _ G h g M).reserve ((min_le_left ..).trans (min_le_right ..)) le_rfl -- tune
 let N:=upMale L ho M; let f(x:Rent0 G e):CapX m B e:=⟨x.val.2,x.property.cg⟩; let y(x:Rent0 G e):CapX r B e:=⟨x.val.1,x.property.fg⟩
 have hz:=gainW G; rw [h] at hz
 have hx:= (F m g N).leaps (q:=w') (c:=dressL G e) (Ω:=LineE n G z e) (Φ:=poolG G) (v:=A) (w:=A) hz f ((continuous_snd.comp continuous_subtype_val).subtype_mk _) t hu.le ((le_div_iff₀ ht).mp (min_le_right ..)) (fun S x y h=>by intro i a b; exact h.2 i (cloud_pool G S a) (cloud_pool G S b)) (fun x g=>⟨scaleG G g,rfl⟩) (fun E _ _ _ V u f t x hx=>(t x hx).2)
 have hy:=(F r (P.clock_fine G g) M).leaps (q:=w') (c:=dressL G e) (Ω:=LineE n G z e) (Φ:=id) (v:=1) (w:=1) (idemX (terr _)) y ((continuous_fst.comp continuous_subtype_val).subtype_mk _) t hu.le (by rw [mul_one]; exact (min_le_left ..).trans (min_le_left ..)) (fun S x y h=>h.1) (fun x y=> ⟨y,rfl⟩) (fun E _ _ _ V u f t x hx=> (t x hx).1)
 rw [one_mul] at hy; have hh:=(he.plus hx).plus hy.minus; simp_rw [altar,sub_eq_add_neg]; exact hh
end YM.CF.Spire
