import YM.CF.Pec.Mite
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra

variable {n X:Side}{k:ℕ}{e d a:ℝ}
def pear (G:Ratio n X) (h:0<e) (u: Nom n X):↥(Broc.Rent0 G e):= open scoped Classical in if p:u∈Broc.Rent0 G e then ⟨u,p⟩ else ⟨1,(near_j G e h).self_of_nhds⟩
lemma pear_even(G: Ratio n X)(p:0<e){x:Nom n X}(h:x∈Broc.Rent0 G e): (pear G p x)=⟨x,h⟩:=dif_pos h
lemma truK{k:ℕ} {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]{U:F→ Op SU.F}{x:F}{r:ℝ}(h: Jet.Allows k U x r): ∀ᶠ y in 𝓝 x,Jet.Allows k U y (r+1):=by
 have he(i: Fin (k+1)):∀ᶠ y in 𝓝 x, ‖iteratedFDeriv ℝ i.val U y‖≤ r+1:=by
    have ht:i.val ≤k:=by omega
    exact (h.smooth.continuousAt_iteratedFDeriv (k:=i.val) (by exact_mod_cast ht)).norm.tendsto.eventually (ge_mem_nhds ((h.norm_le _ ht).trans_lt (by linarith))) -- tune name
 filter_upwards [h.smooth.eventually (by simp),eventually_all.mpr he] with t p hh; exact ⟨p,fun i hi=>hh ⟨i,by omega⟩⟩
lemma glean(k:ℕ):(∃ q:ℝ,0≤q ∧ ∀ {M n: Side}{T:RG.StepData (More M) (More n)}(F:Forest T.ratio),Jet.TransK k (fine SU.group F) 0 q ∧ Jet.TransK k (outer SU.group F) 0 q):=by
 obtain ⟨c,h,H⟩:= hatch k; have he:=dGray_pos h; let X:= (coordL (k:=SU.F)).symm.toContinuousLinearMap; let A:= ‖X‖* dGray c; have hA:0≤A:=mul_nonneg (norm_nonneg X) he
 have ht {Y:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Bkg Y)(u:EnvM k U 0 c): Jet.TransK k U 0 A:=by
    intro i; have hp: Allows k (fun y=>fund (U y i)) 0 A:= (Push.Uniform.allows_pi he fun m:SU.F=> Push.Uniform.allows_pi he fun n:SU.F=> delight U u i m n).linear X le_rfl; exact ⟨hp.analytic.of_le le_top,hp.norm_le⟩
 exact ⟨_,hA,fun F=>⟨ht _ (H F).1,ht _ (H F).2⟩⟩
lemma gather {M n:Side}{T:RG.StepData (More M) (More n)}(F:Forest T.ratio)(k:ℕ)(A:ℝ) (x:Jet.TransK k (fine SU.group F) 0 A)(y:Jet.TransK k (outer SU.group F) 0 A) (p:0<e) (G:Ratio M n):∃ V:Set (Snap F),IsOpen V∧0∈V∧(∀ v∈V, hats F v∈ Broc.Rent0 G e)∧∀ v∈ V, Jet.TransK k (fun i=> (pear G p (hats F i)).val.1) v (A+1) ∧ Jet.TransK k (fun i=>(pear G p (hats F i)).val.2) v (A+1):=by
 have he {N:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{X:E→Bkg N}(p:Jet.TransK k X 0 A):ContinuousAt X 0:= continuousAt_pi.mpr (fun i=> (fund_cont.isClosedEmbedding (show Function.Injective fund from SU.group.mat_injective)).isInducing.continuousAt_iff.mpr (p i).smooth.continuousAt)
 have hp: ∀ᶠ i in 𝓝 0,hats F i∈ Broc.Rent0 G e:=by apply (show ContinuousAt (hats F) 0 from (he x).prodMk (he y)).preimage_mem_nhds (t:=Broc.Rent0 G e); rw [hats0]; exact near_j G e p
 let P(u:Snap F):= hats F u∈ Broc.Rent0 G e ∧ Jet.TransK k (fine SU.group F) u (A+1) ∧ Jet.TransK k (outer SU.group F) u (A+1)
 have hg : {u| P u} ∈ 𝓝 0:= hp.and ((eventually_all.mpr (fun i=> truK (x i))).and (eventually_all.mpr (fun i=>truK (y i))))
 obtain ⟨V,h,m,l⟩:=_root_.mem_nhds_iff.mp hg; have hu z (hz:z∈V): hats F z∈Broc.Rent0 G e:=(h hz : P z).1; refine ⟨V,m,l,hu,fun z hz=>?_⟩
 obtain ⟨u,v⟩:=(h hz : P z).2; constructor; intro i; apply (u i).germ; filter_upwards [m.mem_nhds hz] with t ht; exact congrArg (fun x:↥(Broc.Rent0 G e)=>fund (x.val.1 i)) (pear_even G p (hu _ ht)).symm
 intro i; apply (v i).germ; filter_upwards [m.mem_nhds hz] with t ht; exact congrArg (fun x:↥(Broc.Rent0 G e)=>fund (x.val.2 i)) (pear_even G p (hu _ ht)).symm
-- boundaries coarse
lemma readsV {M n:Side}{T:RG.StepData (More M) (More n)}(F:Forest T.ratio)(G:Ratio M n)(h:T.ratio=ratio G)(p:0<e)(V:Set (Snap F))(u:∀ x∈V,hats F x∈ Broc.Rent0 G e)(S:Seal (Site (More n)))(x:Site (More n))(w:x∈ S)(g:Grove (Tenant.terr _) S){f:↥(Broc.Rent0 G e)→ℂ}(t:Broc.Peak (Broc.dressL G e) S f d): Requests V (fun i=> f (pear G p (hats F i))) (clothH T F) x (S.card+ T.ratio.count.val):=by
 intro i hi j hj hp; change f (pear G p (hats F i))= f (pear G p (hats F j)); rw [pear_even G p (u _ hi),pear_even G p (u _ hj)]; refine t.reads _ _ ⟨fun z a b=>?_,fun z a b=>?_⟩; apply fine_read F hp; exact Nat.add_le_add_right (g.lim _ w _ a|>.le) _
 apply co_read F hp; rw [h]; exact (g.lim _ w _ (mem_filter.mp a).2|>.le).trans (Nat.le_add_right ..)
def pew {G:Ratio n X}(i:Site (More X)):Site n:= ((part n).symm ((ratio G).parent i)).1
lemma peep (G:Ratio n X)(i:Site (More X)):separation ((ratio G).embed (node (pew (G:=G) i))) i ≤ 3*G.count.val:=by
 let v:= ratio G; let x:= v.parent i; let y:= (part n).symm x; have hi: separation (node y.1) x≤ 2:=by rw [show x=poolY y.1 y.2 from ?_]; exact dealU ..; exact (show part n y=x from (part n).apply_symm_apply _).symm
 have he := Broc.scale_span G _ _ 2 hi; have hp := Corona.near v i; refine (separation_triangle _ (v.embed x) _).trans ?_; change separation (v.embed (node y.1)) (v.embed x)+ _≤ _; rw [separation_comm (v.embed x)]; have hg:v.count=G.count:=rfl; change 2*separation i (v.embed x) ≤ _ at hp; rw [hg] at hp; change separation (v.embed _) (v.embed _ ) ≤ _ at he; omega
lemma blink_b {M:Side}{ι E:Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]{U:Positions ι→ E}{l:ι→ Site M}{x y: Site M}(p: Beacon l a k U x 0 d)(r:0≤d)(g:0<a){b:ℕ}(h:separation x y ≤ b):Beacon l a k U y 0 (d* Real.exp (a*(k*b:ℕ))) :=by
 intro i hi v; rw [mul_assoc,← Real.exp_add]; apply (p _ hi v).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) r); have ht:spanSites l y v ≤ k*b + spanSites l x v:=by unfold spanSites; apply le_trans (sum_le_sum (g:=fun j=> b+separation x (l (v j))) fun j _=> (separation_triangle y x (l (v j))).trans (Nat.add_le_add_right ((separation_comm ..).trans_le h) _)); rw [sum_add_distrib]; gcongr; simp [Nat.mul_le_mul_right _ hi]
 have hh: a* ((spanSites l y v):ℝ)≤ a*( (k*b:ℕ) + (spanSites l x v:ℕ) :ℝ):=by apply mul_le_mul_of_nonneg_left _ g.le; exact_mod_cast ht
 linarith
end YM.CF.Pec
