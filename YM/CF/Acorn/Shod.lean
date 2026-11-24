import YM.CF.Acorn.Brittle
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(S:Broc.Table m B)
def MonoX(m B:Side)(e:ℝ)(S:Broc.Table m B): Set (Bool→Skin m B):={x|(∀ i, Guard (x i) e)∧ Agrees (Sᶜ:Finset _) (x false) (x true)}
abbrev Castle(m B: Side)(e:ℝ)(S:Broc.Table m B):= ↥(MonoX m B e S)
instance castleB : CompactSpace (Castle m B e S) :=by
 apply isCompact_iff_compactSpace.mp
 let f:=fun i:Bool=>{x:Bool→ Skin m B| Guard (x i) e}; let A: Set (Bool→Skin m B):={x|Agrees (Sᶜ:Finset _) (x false) (x true)}
 have he(i):IsClosed (f i):= (cover_closed (Domain m B) e).preimage (show Continuous (fun f:Bool→Skin m B=>f i) from continuous_apply i)
 have hk:MonoX m B e S=(⋂ i,f i) ∩ A:=by ext i; simp [MonoX,A,f]
 have hv:IsClosed A:=by
    let T:Set (Edge (Site (Domain m B))):={i|i.1∈Sᶜ ∧ i.1+step i.2 ∈ Sᶜ}
    rw [show A =⋂ i∈T,{x:Bool→Skin m B|x false i=x true i} from by ext; simp [A,T,Agrees]]
    exact isClosed_biInter fun i _=>isClosed_eq (by fun_prop) (by fun_prop)
 rw [hk]; exact ((isClosed_iInter he).inter hv).isCompact -- rw changes instance? tune

def fars(m B:Side)(S:Broc.Table m B):= complexA m B Sᶜ
def inky(m B:Side)(S:Broc.Table m B)(i:Bool)(a:Index m): Bool×Index m := (if a∈ fars m B S then false else i,a)
def marr (S:Broc.Table m B)(i:Bool)(w:I (Index m)→Ballot): Cue m:=w ∘ inky m B S i
lemma inky_st(S:Broc.Table m B)(i:Bool): Injective (inky m B S i):= fun a b e=> congrArg Prod.snd e
lemma marr_c(i:Bool): Continuous (marr S i):= continuous_pi fun a=>continuous_apply _
lemma marr_same(t:I (Index m)→ Ballot)(i j:Bool) : AgreeF (fars m B S) (marr S i t) (marr S j t):=fun k h=> by simp [marr,inky,h]
lemma reform (i: Bool)(v:I (Index m)→ Ballot)(a: Index m)(p:Ballot):marr S i (update v (inky m B S i a) p)=update (marr S i v) a p:=by
 funext x; by_cases h:x=a; simp [marr,h]; rw [update_of_ne h]; exact update_of_ne (fun f=>h (inky_st S i f)) ..

def Shorn (S:Broc.Table m B)(x: Castle m B e S): Plan (I (Index m)) cloud where
 orderF := fun i=> degree m i.2
 indexF := fun i=> if inky m B S i.1 i.2=i then (faces m i.2).image (inky m B S i.1) else ∅
 run := fun i t=> if inky m B S i.1 i.2=i then water m B (x.val i.1) i.2 (marr S i.1 t) else 1
 polite i :=by split; exact ((Phase.rock m B _).polite _).comp (marr_c S _); exact continuous_const
 rightF i w:=by split; exact water_pos ..; exact zero_le_one
 normalize i v:=by split_ifs with hx; simp_rw [←show ∀ p,update (marr S i.1 v) i.2 p=marr S i.1 (update v i p) from fun p=>(reform S i.1 v i.2 p|>.symm.trans (by rw [hx]))]; exact water_norm ..; simp
 readF i x y h:=by split_ifs with hx; rw [if_pos hx] at h; exact (Phase.rock m B _).readF _ _ _ (fun k p=>h _ (mem_image_of_mem _ p)); rfl
 before i j p h:=by
    split_ifs at p with hx; swap; simp at p
    obtain ⟨a,g,rfl⟩:=mem_image.mp p; exact fits_degree (mem_filter.mp g).2 (fun e=> h ((by rw [show a=i.2 from e,hx] : inky m B S i.1 a=i).symm))
lemma run_eq(i)(x: Castle m B e S) (t:I (Index m)→Ballot) : (Shorn S x).run i t=if inky m B S i.1 i.2=i then water m B (x.val i.1) i.2 (marr S i.1 t) else 1:=rfl
lemma run_c (i:I (Index m)) : Continuous (fun x:Castle m B e S × (I (Index m)→Ballot)=> (Shorn S x.1).run i x.2):=by
 simp_rw [run_eq]; by_cases h:inky m B S i.1 i.2=i; swap; simp only [if_neg h]; exact continuous_const
 simp only [if_pos h] -- tune
 let F:=fun x:Castle m B e S × (I (Index m)→Ballot)=> (x.1.val i.1,marr S i.1 x.2)
 have he: Continuous F := ((show Continuous (fun x:Bool→Skin m B=> x i.1) from continuous_apply _).comp (continuous_subtype_val.comp continuous_fst)).prodMk ((marr_c S _).comp continuous_snd)
 have ht:=(water_cont m B i.2).comp he; exact ht
lemma sh_c:Continuous (fun x: Castle m B e S × (I (Index m)→Ballot)=> fall (Shorn S x.1) x.2) := continuous_finsetProd (f:=fun i (x:Castle m B e S × (I (Index m)→Ballot))=> (Shorn S x.1).run i x.2) _ (fun i _=>run_c S i)
lemma lake (x:Castle m B e S) (t:I (Index m)→Ballot)(h: fall (Shorn S x) t≠0)(i:Bool): ZeroF m B (x.val i) (marr S i t):=by
 let F:= Shorn S x
 apply law_rich; rw [base_pl]; apply Finset.prod_ne_zero_iff.mpr; intro j _
 let y:= inky m B S i j
 have ht: F.run y t≠0:= prod_ne_zero_iff.mp h _ (mem_univ y) -- tune
 change (if inky m B S y.1 y.2=y then water _ _ _ _ _ else _)≠0 at ht; change water m B _ j _≠0
 by_cases p:j∈ fars m B S; swap; simpa only [F,y,inky,p,ite_false,ite_true] using ht
 rw [show y=(false,j) from by simp [y,inky,p]] at ht; rw [if_pos] at ht; swap; simp [inky,p]
 cases i; exact ht
 let A:=faces m j; have hg: AgreeF A (marr S false t) (marr S true t):= (marr_same S t false true).less (complex_down m B _ j p)
 exact (water_limit _ _ j _ _ hg (fun i v q=> x.property.2 i ((mem_filter.mp p).2 v) ((mem_filter.mp p).2 q))) ▸ (ht : water m B _ j (marr S false t) ≠0)
end YM.CF.Acorn
