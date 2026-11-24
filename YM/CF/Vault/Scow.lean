import YM.CF.Vault.Hill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N P:Side}{ι:Type*}{A B C:Chop ι}{n l:ℕ}
lemma joyful (t:Side) (p:0<n) (k:Joy t A B n)(h:n≤l): Joy t A B l:=by
 apply Still.forward k; intro N P G hG x s i v; refine ⟨(s i v).1,fun j u=> (s i v).2 j ?_⟩; apply u.trans; gcongr
variable (j:ℕ)(L:Side)(ho:Odd L.val)(p:1≤j)(e:Even j)(b:Bool)
abbrev authority{n l:ℕ}(b:Bool){N P:Side}(G:Ratio N P)(x:Sew N P)(i:Duel):Prop := Stay (umber j L ho b i G (post x)) (tonic (umber j L ho b) (zoom j L ho b) i G (post x)) n ∧ Stay (lobe G b) (tonic (P:=lendX b) (slackX j b) i G (post x)) l -- args k implicit not variable
include ho p e
lemma status' (h:Joy L (umber j L ho b) (zoom j L ho b) n)(k:Joy L (lendX b) (slackX j b) l): Still L fun G x=>∀ i:Duel,authority (n:=n) (l:=l) j L ho b G x i:=by
 have he {P Q A:Chop Duel}(p:Land L P Q A) (i:ℕ)(h:Joy L P Q i): Still L (fun G x=>∀ v,Stay (P v G (post x)) (tonic P Q v G (post x)) i):=by
   refine (p.sky.plus h).forward ?_; intro N F G hp x u v a l t s
   let H:=railIn i a l s; let y:TickZ:=⟨t,H⟩; have hx:= (u.1 v).1
   refine ⟨straight_skew hx (skew_square G false x) (skew_square G true x) _, (u.2 v y).1,?_⟩
   let A': TickZ:=⟨berth i a,railIn i a l ⟨le_rfl,ber_m i a.le_succ⟩⟩; exact ((u.2 v A').2 y (berth_jump (by omega) a s)).trans_lt (by norm_num)
 apply ((he (land_v j L ho p e b) n h).plus (he (land_p j L ho p e b) l k)).forward; intro N P G h x s i; exact ⟨s.1 i,s.2 i⟩
abbrev Tollday (n l:ℕ)(x:Sew N P)(G:Ratio N P):Prop:=∀ m,Safe (scrap true (coast j) m G (post x))∧ Safe (scrap false (urban j L ho) m G (post x)) ∧ IsUnit (dustX j m G (post x))∧∀ b:Bool, Commuting j L ho b G x m ∧ authority (n:=n) (l:=l) j L ho b G x m
structure Tollage(n l:ℕ):Prop where
 p:0<n
 lpos:0<l
 hd : Joy L (umber j L ho true) (zoom j L ho true) n
 hm: Joy L (umber j L ho false) (zoom j L ho false) n
 hx: Joy L (lendX true) (slackX j true) l
 hc: Joy L (lendX false) (slackX j false) l
lemma taxed: ∃ n l:ℕ, Tollage j L ho n l:=by
 obtain ⟨n,hn,Y⟩:= (land_v j L ho p e true).youth ho; obtain ⟨l,hl,K⟩:= (land_v j L ho p e false).youth ho; obtain ⟨c,t,hc⟩:=(land_p j L ho p e true).youth ho; obtain ⟨b,s,V⟩:= (land_p j L ho p e false).youth ho
 exact ⟨max n l,max c b,lt_max_of_lt_left hn,lt_max_of_lt_left t,joyful L hn Y (le_max_left ..),joyful L hl K (le_max_right ..),joyful L t hc (le_max_left ..),joyful L s V (le_max_right ..)⟩
lemma deserving (h:Tollage j L ho n l):Still L fun G x=>Tollday j L ho n l x G:=by
 let Y(b):= vintage j L ho p e b
 apply ((((Y true).plus (Y false)).plus ((status' j L ho p e true h.hd h.hx).plus (status' j L ho p e false h.hm h.hc))).plus ((emin j L ho p e).plus (stable_j j L ho e).2.2)).forward; rintro N P G hk x ⟨⟨A,B⟩,t,w⟩ i
 refine ⟨(t i).1,(t i).2,w i,fun b=>?_⟩; cases b; exact ⟨A.2 i,B.2 i⟩; exact ⟨A.1 i,B.1 i⟩
end YM.CF.Vault
