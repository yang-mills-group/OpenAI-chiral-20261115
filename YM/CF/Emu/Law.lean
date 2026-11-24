import YM.CF.Emu.Fame
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory Vale RG Wilson Scree Skye
variable {α:Type*}{N:Side}{o:Site N}
-- Wilson dressing. gauge
variable {t:Site (More N)→E}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}
def zoneA(o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(z:α→TagT)(L:List α):=Emu.train (fun x=>nac o U t R (z x)) L
def matchF(o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(z:α→TagT)(L:List α)(q:Wave (Single N)):ℂ:=inner ℂ (mateK N) (acts (zoneA o U t R z L) q)
def wall(o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(z:α→TagT)(L:List α)(q:Wave (Single N))(x:ℂ):= matchF o U t R z L q-inner ℂ (mateK N) q*x
lemma barter(U:Bkg (More N))(t:E)(R:ℝ)(o:Site N)(g:Site (More N)→E)(a:TagT): nac o (gauge g U) (g (node o)*t) R a= whisk (tradew N g) (nac o U t R a):=by
 unfold whisk nac; dsimp only; rw [hike]; congr 1; split_ifs; rw [map_neg,map_smul]; rw [map_smul]
lemma must(o:Site N)(U:Bkg (More N))(g:Cart (More N))(t:E)(R:ℝ)(a:α→ TagT)(J:List α):zoneA o (gauge g U) (g (node o)*t) R a J= twist (quantU (tradew N g)) (zoneA o U t R a J):=by
 let A:= tradew N g; let F:=zoneA o U t R a
 induction J with
 | nil=>simp [zoneA,Emu.train,rollC]
 | cons i J H=>
   let x:=nac o U t R (a i); change ton (nac _ _ _ _ (a i))* zoneA _ _ _ R a J= twist _ (ton x*F J); rw [barter, H,map_mul]; congr 1
   have ht(i:Reader0 (Single N)): ton (whisk A i)=twist (quantU A) (ton i):=by rcases i with ⟨t,x⟩; cases t; exact (twist_create ..).symm; exact (twist_remove ..).symm
   exact ht x
lemma oak_k(o:Site N)(U:Bkg (More N))(g:Cart (More N))(t:E)(R:ℝ)(a:α→ TagT)(J:List α)(q:Wave (Single N)): matchF o (gauge g U) (g (node o)*t) R a J (Fone (tradew _ g) q)=matchF o U t R a J q:=by
 unfold matchF; rw [must]; let B:=quantU (tradew N g); let A:=zoneA o U t R a J; let p:=mateK N
 change inner ℂ _ (acts (twist B A) (acts B.val q))=_; rw [show acts (twist B A) _ = acts B.val (acts A q) from (Fock.swivel B A q).symm]; nth_rw 1 [←show acts B.val (mateK N)=_ from Girt.mastC g]; exact act_unit_inner B _ _
local notation "Aᵐ"=> CSide m B
lemma noteR (D:Span H K b v c l r n)(u:n ≤ Aᵐ.val)(U:Bkg (Domain m B))(w:Guard U e)(g:Cart (Domain m B))(M:Jill.Male)(o:Site Aᵐ)(s:E)(R:ℝ)(z:α→TagT)(J:List α)(x:ℂ): wall o (gauge g U) (g (node o)*s) R z J (changeM (m:=m) P (gauge g U) M) x= wall o U s R z J (changeM P U M) x:=by
 have ht:Fone (tradew _ g) (changeM P U M)=changeM P (gauge g U) M:= (Hive.honey_x (m:=m) (M:=M) H D.stmt (D.plan m u).1 D.p w g).symm
 unfold wall; rw [← ht,oak_k]; congr 2 -- tune
 nth_rw 1 [← show acts (quantU (tradew Aᵐ g)).val (mateK Aᵐ)=_ from Girt.mastC g]; exact act_unit_inner (quantU _) _ _
lemma stax(o:Site N)(U:Bkg (More N))(s:E)(R:ℝ)(z:α→TagT)(L:List α)(q:Wave (Single N))(x:ℂ) : wall o U s R z L q x= Plot.stanza 1 q (fun i=>nac o U s R (z i)) L x:=by unfold wall Plot.stanza pRead matchF skyGlow zoneA Emu.train; rw [quant_one,mul_one,act_one]; simp only [rollC,List.map_map]
lemma cityH(o:Site N)(R:ℝ)(z:α→TagT)(L:List α): Continuous fun x:Bkg (More N)×E=>zoneA o x.1 x.2 R z L:=by
 have he(a:TagT): Continuous fun x:Bkg (More N) × E=> hint o a.1 a.2 x.1 x.2:=by
    unfold hint; simp_rw [show ∀ p:E,acts (cote (N:=N) (matter p)).val (basisKet (hub a.2 o a.1))=_ from fun i=> tint _ _ _ i]; refine Continuous.const_smul (g:=fun x:Bkg (More N)× E=>∑ i,(matter (stemF o a.1 a.2 x.1 x.2)).val i a.2.x • basisKet ((hub a.2 o a.1).1,i)) ?_ (wind o a.1); apply continuous_finsetSum; intro i _; refine Continuous.smul (f:=fun x:Bkg (More N)×E=> (matter (stemF o a.1 a.2 x.1 x.2)).val i a.2.x) ?_ (g:=fun _=> basisKet ((hub a.2 o a.1).1,i)) continuous_const
    let F(x:Bkg (More N)×E):= stemF o a.1 a.2 x.1 x.2; have hp:Continuous F:=by unfold F stemF; exact Continuous.mul (Continuous.inv ((continuous_travel ..).comp continuous_fst)) continuous_snd
    exact ((matter_cont.comp hp).matrix_elem i a.2.x)
 induction L with
 | nil=> exact continuous_const
 | cons i l ih=>
   let F(x:Bkg (More N)× E):= ton (nac o x.1 x.2 R (z i)); have hp:Continuous F:=by
      have hv: Continuous fun x:Bkg (More N)× E=> gain R • hint o (z i).1 (z i).2 x.1 x.2:= (he (z i)).const_smul (gain R); unfold F ton nac creed; dsimp only; split_ifs; exact Continuous.star (create_cont.comp hv.neg); exact create_cont.comp hv
   exact hp.mul ih
end YM.CF.Emu
