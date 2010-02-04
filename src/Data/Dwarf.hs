-- | Parses the DWARF 2 and DWARF 3 specifications at http://www.dwarfstd.org given
-- the debug sections in ByteString form.
module Data.Dwarf ( parseDwarfInfo
                  , parseDwarfAranges
                  , parseDwarfPubnames
                  , parseDwarfPubtypes
                  , parseDwarfMacInfo
                  , parseDwarfRanges
                  , parseDwarfLoc
                  , parseDwarfLine
                  , parseDwarfFrame
                  , parseDW_OP
                  , dw_ate
                  , dw_ds
                  , dw_end
                  , dw_access
                  , dw_vis
                  , dw_virtuality
                  , dw_lang
                  , dw_inl
                  , dw_cc
                  , dw_ord
                  , dw_dsc
                  , (!?)
                  , DwarfReader(..)
                  , DIE(..)
                  , DW_CFA(..)
                  , DW_MACINFO(..)
                  , DW_CIEFDE(..)
                  , DW_OP(..)
                  , DW_TAG(..)
                  , DW_AT(..)
                  , DW_ATVAL(..)
                  , DW_LNE(..)
                  , DW_ATE(..)
                  , DW_DS(..)
                  , DW_END(..)
                  , DW_ACCESS(..)
                  , DW_VIS(..)
                  , DW_VIRTUALITY(..)
                  , DW_LANG(..)
                  , DW_ID(..)
                  , DW_INL(..)
                  , DW_CC(..)
                  , DW_ORD(..)
                  , DW_DSC(..)
                  ) where

import Data.Int
import Data.Bits
import Data.Word
import Data.Dynamic
import Data.Binary
import Data.Binary.Get
import Data.Maybe
import Data.Char
import Control.Monad
import Control.Applicative
import qualified Data.Map as M
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as L

---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Utility functions.
---------------------------------------------------------------------------------------------------------------------------------------------------------------

-- Repeatedly perform the get operation until the boolean fails.
getWhile :: (a -> Bool) -> Get a -> Get [a]
getWhile cond get = do
    el <- get
    if cond el then
        liftM (el :) $ getWhile cond get
     else
        return []

-- Decode a NULL-terminated UTF-8 string.
getNullTerminatedString :: Get String
getNullTerminatedString2 = liftM (C.unpack . B.pack) (getWhile (/= 0) getWord8)
getNullTerminatedString = liftM (map (chr . fromIntegral)) $ getWhile (/= 0) getCharUTF8
    where getCharUTF8 = do
            let getCharUTF82 b1 = do
                    b2 <- liftM fromIntegral getWord8 :: Get Word32
                    if b2 .&. 0xc0 == 0x80 then
                            return $ ((b1 .&. 0x1f) `shiftL` 6) .|. (b2 .&. 0x3f)
                         else
                            fail "Invalid second byte in UTf8 string."
                getCharUTF83 b1 = do
                    b2 <- liftM fromIntegral getWord8 :: Get Word32
                    b3 <- liftM fromIntegral getWord8 :: Get Word32
                    if b2 .&. 0xc0 == 0x80 && b3 .&. 0xc0 == 0x80 then
                            return $ ((b1 .&. 0x0f) `shiftL` 12) .|. ((b2 .&. 0x3f) `shiftL` 6) .|. (b3 .&. 0x3f)
                         else
                            fail "Invalid second or third byte in UTf8 string."
                getCharUTF84 b1 = do
                    b2 <- liftM fromIntegral getWord8 :: Get Word32
                    b3 <- liftM fromIntegral getWord8 :: Get Word32
                    b4 <- liftM fromIntegral getWord8 :: Get Word32
                    if b2 .&. 0xc0 == 0x80 && b3 .&. 0xc0 == 0x80 && b4 .&. 0xc0 == 0x80 then
                            return $ ((b1 .&. 0x07) `shiftL` 18) .|. ((b2 .&. 0x3f) `shiftL` 12) .|. ((b3 .&. 0x3f) `shiftL` 6) .|. (b4 .&. 0x3f)
                         else
                            fail "Invalid second or third byte in UTf8 string."
            b1 <- liftM fromIntegral getWord8 :: Get Word32
            case b1 of
                n | n .&. 0x80 == 0x00 -> return $ fromIntegral n
                n | n .&. 0xe0 == 0xc0 -> getCharUTF82 n
                n | n .&. 0xf0 == 0xe0 -> getCharUTF83 n
                n | n .&. 0xf8 == 0xf0 -> getCharUTF84 n
                _                      -> fail "Invalid first byte in UTF8 string."
 
-- Decode a signed little-endian base 128 encoded integer.
getSLEB128 :: Get Int64
getSLEB128 =
    let go acc shift = do
        byte <- liftM fromIntegral getWord8 :: Get Word64
        temp <- return $ acc .|. (clearBit byte 7 `shiftL` shift)
        if testBit byte 7 then
            go temp (shift + 7)
         else
            if shift < 32  && testBit byte 6 then
                return $ fromIntegral $ temp .|. ((-1) `shiftL` shift)
             else
                return $ fromIntegral temp
    in go 0 0

-- Decode an unsigned little-endian base 128 encoded integer.
getULEB128 :: Get Word64
getULEB128 =
    let go acc shift = do
        byte <- liftM fromIntegral getWord8 :: Get Word64
        temp <- return $ acc .|. (clearBit byte 7 `shiftL` shift)
        if testBit byte 7 then
            go temp (shift + 7)
         else
            return temp
    in go 0 0

-- Decode the DWARF size header entry, which specifies both the size of a DWARF subsection and whether this section uses DWARF32 or DWARF64.
getDwarfUnitLength :: DwarfEndianReader -> Get (DwarfEndianSizeReader, Word64)
getDwarfUnitLength dr@(DwarfEndianReader e w16 w32 w64) = do
    size <- w32
    if size == 0xffffffff then do
        size <- w64
        return (dwarfEndianSizeReader True dr, size)
     else if size >= 0xffffff00 then
        fail ("Invalid DWARF size " ++ show size)
      else
        return (dwarfEndianSizeReader False dr, fromIntegral $ size)


---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- DWARF decoder records.
---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Intermediate data structure for a partial DwarfReader.
data DwarfEndianReader = DwarfEndianReader Bool (Get Word16) (Get Word32) (Get Word64)
dwarfEndianReader True  = DwarfEndianReader True  getWord16le getWord32le getWord64le
dwarfEndianReader False = DwarfEndianReader False getWord16be getWord32be getWord64be

-- Intermediate data structure for a partial DwarfReader.
data DwarfEndianSizeReader = DwarfEndianSizeReader Bool (Get Word16) (Get Word32) (Get Word64) Bool Word64 (Get Word64)
dwarfEndianSizeReader True  (DwarfEndianReader e w16 w32 w64) = DwarfEndianSizeReader e w16 w32 w64 True  0xffffffffffffffff w64
dwarfEndianSizeReader False (DwarfEndianReader e w16 w32 w64) = DwarfEndianSizeReader e w16 w32 w64 False 0xffffffff (liftM fromIntegral w32)

-- | Type containing functions and data needed for decoding DWARF information.
data DwarfReader = DwarfReader
    { littleEndian          :: Bool       -- ^ True for little endian encoding.
    , dwarf64               :: Bool       -- ^ True for 64-bit DWARF encoding.
    , target64              :: Bool       -- ^ True for 64-bit pointers on target machine.
    , largestOffset         :: Word64     -- ^ Largest permissible file offset.
    , largestTargetAddress  :: Word64     -- ^ Largest permissible target address.
    , getWord16             :: Get Word16 -- ^ Action for reading a 16-bit word.
    , getWord32             :: Get Word32 -- ^ Action for reading a 32-bit word.
    , getWord64             :: Get Word64 -- ^ Action for reading a 64-bit word.
    , getDwarfOffset        :: Get Word64 -- ^ Action for reading a offset for the DWARF file.
    , getDwarfTargetAddress :: Get Word64 -- ^ Action for reading a pointer for the target machine.
    }
instance Show DwarfReader where
    show dr = "DwarfReader " ++ show (littleEndian dr) ++ " " ++ show (dwarf64 dr) ++ " " ++ show (target64 dr) 
instance Eq DwarfReader where
    a1 == a2 = (littleEndian a1 == littleEndian a2) && (dwarf64 a1 == dwarf64 a2) && (target64 a1 == target64 a2)
dwarfReader True  (DwarfEndianSizeReader e w16 w32 w64 d lo sz) = DwarfReader e d True lo 0xffffffffffffffff w16 w32 w64 sz w64
dwarfReader False (DwarfEndianSizeReader e w16 w32 w64 d lo sz) = DwarfReader e d False lo 0xffffffff w16 w32 w64 sz (liftM fromIntegral w32)

---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- Abbreviation and form parsing
---------------------------------------------------------------------------------------------------------------------------------------------------------------
getForm dr str cu form = getForm_ dr str cu form
getForm_ dr str cu DW_FORM_addr      = pure (DW_ATVAL_UINT . fromIntegral) <*> (getDwarfTargetAddress dr)
getForm_ dr str cu DW_FORM_block1    = liftM fromIntegral getWord8       >>= getByteString >>= return . DW_ATVAL_BLOB
getForm_ dr str cu DW_FORM_block2    = liftM fromIntegral (getWord16 dr) >>= getByteString >>= return . DW_ATVAL_BLOB
getForm_ dr str cu DW_FORM_block4    = liftM fromIntegral (getWord32 dr) >>= getByteString >>= return . DW_ATVAL_BLOB
getForm_ dr str cu DW_FORM_block     = liftM fromIntegral getULEB128     >>= getByteString >>= return . DW_ATVAL_BLOB
getForm_ dr str cu DW_FORM_data1     = pure (DW_ATVAL_UINT . fromIntegral) <*> getWord8
getForm_ dr str cu DW_FORM_data2     = pure (DW_ATVAL_UINT . fromIntegral) <*> (getWord16 dr)
getForm_ dr str cu DW_FORM_data4     = pure (DW_ATVAL_UINT . fromIntegral) <*> (getWord32 dr)
getForm_ dr str cu DW_FORM_data8     = pure (DW_ATVAL_UINT . fromIntegral) <*> (getWord64 dr)
getForm_ dr str cu DW_FORM_udata     = pure DW_ATVAL_UINT <*> getULEB128
getForm_ dr str cu DW_FORM_sdata     = pure DW_ATVAL_INT <*> getSLEB128
getForm_ dr str cu DW_FORM_flag      = pure (DW_ATVAL_BOOL . (/= 0)) <*> getWord8
getForm_ dr str cu DW_FORM_string    = pure DW_ATVAL_STRING <*> getNullTerminatedString
getForm_ dr str cu DW_FORM_ref1      = pure (DW_ATVAL_UINT . (+) cu) <*> liftM fromIntegral getWord8
getForm_ dr str cu DW_FORM_ref2      = pure (DW_ATVAL_UINT . (+) cu) <*> liftM fromIntegral (getWord16 dr)
getForm_ dr str cu DW_FORM_ref4      = pure (DW_ATVAL_UINT . (+) cu) <*> liftM fromIntegral (getWord32 dr)
getForm_ dr str cu DW_FORM_ref8      = pure (DW_ATVAL_UINT . (+) cu) <*> liftM fromIntegral (getWord64 dr)
getForm_ dr str cu DW_FORM_ref_udata = pure (DW_ATVAL_UINT . (+) cu) <*> liftM fromIntegral getULEB128
getForm_ dr str cu DW_FORM_ref_addr  = pure DW_ATVAL_UINT <*> getDwarfOffset dr
getForm_ dr str cu DW_FORM_indirect  = getULEB128 >>= getForm dr str cu . dw_form
getForm_ dr str cu DW_FORM_strp      = do
    offset <- liftM fromIntegral (getDwarfOffset dr)
    return $ DW_ATVAL_STRING $ runGet getNullTerminatedString (L.fromChunks [B.drop offset str])

data DW_ABBREV = DW_ABBREV
    { abbrevNum       :: Word64
    , abbrevTag       :: DW_TAG
    , abbrevChildren  :: Bool
    , abbrevAttrForms :: [(DW_AT, DW_FORM)]
    }

getAbbrevList :: Get [(Word64, DW_ABBREV)]
getAbbrevList =
  do abbrev <- getULEB128
     if abbrev == 0
       then return []
       else do tag       <- getDW_TAG
               children  <- liftM (== 1) getWord8
               attrForms <- getAttrFormList
               xs <- getAbbrevList
               return  ((abbrev, DW_ABBREV abbrev tag children attrForms) : xs)
  where
  getAttrFormList = liftM (map (\(x,y) -> (dw_at x, dw_form y)))
                  $ getWhile (/= (0,0)) (liftM2 (,) getULEB128 getULEB128)


---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- DWARF information entry and .debug_info section parsing.
---------------------------------------------------------------------------------------------------------------------------------------------------------------
-- | The dwarf information entries form a graph of nodes tagged with attributes. Please refer to the DWARF specification
-- for semantics. Although it looks like a tree, there can be attributes which have adjacency information which will
-- introduce cross-branch edges.
data DIE = DIE
    { dieId           :: Word64              -- ^ Unique identifier for this entry.
    , dieParent       :: Maybe Word64        -- ^ Unique identifier of this entry's parent.
    , dieChildren     :: [Word64]            -- ^ Unique identifiers of this entry's children.
    , dieSiblingLeft  :: Maybe Word64        -- ^ Unique identifier of the left sibling in the DIE tree, if one exists.
    , dieSiblingRight :: Maybe Word64        -- ^ Unique identifier of the right sibling in the DIE tree, if one exists.
    , dieTag          :: DW_TAG              -- ^ Type tag.
    , dieAttributes   :: [(DW_AT, DW_ATVAL)] -- ^ Attribute tag and value pairs.
    , dieReader       :: DwarfReader         -- ^ Decoder used to decode this entry. May be needed to further parse attribute values.
    } deriving (Show, Eq)

-- | Utility function for retrieving the list of values for a specified attribute from a DWARF information entry.
(!?) :: DIE -> DW_AT -> [DW_ATVAL]
(!?) die at = map snd $ filter (\(a,v) -> a == at) $ dieAttributes die

-- Decode a non-compilation unit DWARF information entry, its children and its siblings.
getDieTree parent lsibling abbrev_map dr str_section cu_offset = do
    offset <- liftM fromIntegral bytesRead
    abbrid <- getULEB128
    if abbrid == 0 then
        return []
     else do
        let abbrev         = abbrev_map M.! abbrid
            tag            = abbrevTag abbrev
            has_children   = abbrevChildren abbrev
            (attrs, forms) = unzip $ abbrevAttrForms abbrev
        values    <- mapM (getForm dr str_section cu_offset) forms
        ancestors <- if has_children then getDieTree (Just offset) Nothing abbrev_map dr str_section cu_offset else return []
        siblings  <- getDieTree parent (Just offset) abbrev_map dr str_section cu_offset
        let children = map dieId $ filter (\x -> if isJust (dieParent x) then fromJust (dieParent x) == offset else False) ancestors
            rsibling = if null siblings then Nothing else Just $ dieId $ head siblings
        return $ (DIE offset parent children lsibling rsibling tag (zip attrs values) dr : ancestors) ++ siblings

-- Decode the compilation unit DWARF information entries.
getDieCus cu_lsibling odr abbrev_section str_section = do
    empty <- isEmpty
    if empty then
        return []
     else do
        cu_offset       <- liftM fromIntegral bytesRead
        (dr@(DwarfEndianSizeReader _ w16 _ _ _ _ sz), _) <- getDwarfUnitLength odr
        version         <- w16
        abbrev_offset   <- sz
        addr_size       <- getWord8
        dr              <- return $ case addr_size of
                            4 -> dwarfReader False dr
                            8 -> dwarfReader True dr
        cu_die_offset   <- liftM fromIntegral bytesRead
        cu_abbr_num     <- getULEB128
        let abbrev_table         = B.drop (fromIntegral abbrev_offset) abbrev_section
            abbrev_map           = M.fromList $ runGet getAbbrevList $ L.fromChunks [abbrev_table]
            cu_abbrev            = abbrev_map M.! cu_abbr_num
            cu_tag               = abbrevTag cu_abbrev
            cu_has_children      = abbrevChildren cu_abbrev
            (cu_attrs, cu_forms) = unzip $ abbrevAttrForms cu_abbrev
        cu_values    <- mapM (getForm dr str_section cu_offset) cu_forms
        cu_ancestors <- if cu_has_children then getDieTree (Just cu_die_offset) Nothing abbrev_map dr str_section cu_offset else return []
        cu_siblings  <- getDieCus Nothing odr abbrev_section str_section
        let cu_children = map dieId $ filter (\x -> if isJust (dieParent x) then fromJust (dieParent x) == cu_offset else False) cu_ancestors
            cu_rsibling = if null cu_siblings then Nothing else Just $ dieId $ head cu_siblings
        return $ (DIE cu_die_offset Nothing cu_children cu_lsibling cu_rsibling cu_tag (zip cu_attrs cu_values) dr : cu_ancestors) ++ cu_siblings

-- | Parses the .debug_info section (as ByteString) using the .debug_abbrev and .debug_str sections.
parseDwarfInfo :: Bool             -- ^ True for little endian target addresses. False for big endian.
               -> B.ByteString     -- ^ ByteString for the .debug_info section.
               -> B.ByteString     -- ^ ByteString for the .debug_abbrev section.
               -> B.ByteString     -- ^ ByteString for the .debug_str section.
               -> M.Map Word64 DIE -- ^ A map from the unique ids to their corresponding DWARF information entries.
parseDwarfInfo littleEndian info_section abbrev_section str_section =
    let dr = dwarfEndianReader littleEndian
        di = runGet (getDieCus Nothing dr abbrev_section str_section) $ L.fromChunks [info_section]
    in M.fromList $ zip (map dieId di) di

-- Section 7.19 - Name Lookup Tables
getNameLookupEntries :: DwarfReader -> Word64 -> Get [(String, [Word64])]
getNameLookupEntries dr cu_offset = do
    die_offset <- getDwarfOffset dr
    if die_offset == 0 then
        return []
     else do
        name <- getNullTerminatedString
        rest <- getNameLookupEntries dr cu_offset
        return $ (name, [cu_offset + die_offset]) : rest

getNameLookupTable :: Bool -> DwarfEndianReader -> Get [M.Map String [Word64]]
getNameLookupTable target64 odr = do
    empty <- isEmpty
    if empty then
        return []
     else do
        (dr, _)           <- getDwarfUnitLength odr
        dr                <- return $ dwarfReader target64 dr
        version           <- getWord16 dr
        debug_info_offset <- getDwarfOffset dr
        debug_info_length <- getDwarfOffset dr
        pubNames          <- liftM (M.fromListWith (++)) (getNameLookupEntries dr debug_info_offset)
        rest              <- getNameLookupTable target64 odr
        return $ pubNames : rest

-- | Parses the .debug_pubnames section (as ByteString) into a map from a value name to a debug info id in the DwarfInfo.
parseDwarfPubnames :: Bool -> Bool -> B.ByteString -> M.Map String [Word64]
parseDwarfPubnames littleEndian target64 pubnames_section =
    let dr = dwarfEndianReader littleEndian
    in M.unionsWith (++) $ runGet (getNameLookupTable target64 dr) $ L.fromChunks [pubnames_section]

-- | Parses the .debug_pubtypes section (as ByteString) into a map from a type name to a debug info id in the DwarfInfo.
parseDwarfPubtypes :: Bool -> Bool -> B.ByteString -> M.Map String [Word64]
parseDwarfPubtypes littleEndian target64 pubtypes_section =
    let dr = dwarfEndianReader littleEndian
    in M.unionsWith (++) $ runGet (getNameLookupTable target64 dr) $ L.fromChunks [pubtypes_section]

-- Section 7.20 - Address Range Table
getAddressRangeTable target64 odr = do
    empty <- isEmpty
    if empty then
        return []
     else do
        (dr, _)           <- getDwarfUnitLength odr
        dr                <- return $ dwarfReader target64 dr
        version           <- getWord16 dr
        debug_info_offset <- getDwarfOffset dr
        address_size      <- liftM fromIntegral getWord8
        segment_size      <- liftM fromIntegral getWord8
        bytes_read        <- bytesRead
        skip $ fromIntegral (2 * address_size - (bytes_read `mod` (2 * address_size)))
        address_ranges    <- case address_size of
                            4 -> getWhile (/= (0, 0)) (liftM2 (,) (liftM fromIntegral (getWord32 dr)) (liftM fromIntegral (getWord32 dr)))
                            8 -> getWhile (/= (0, 0)) (liftM2 (,) (getWord64 dr) (getWord64 dr))
                            n -> fail ("Unrecognized address size " ++ show address_size ++ " in .debug_aranges section.")
        rest              <- getAddressRangeTable target64 odr
        return $ (address_ranges, debug_info_offset) : rest

-- | Parses  the .debug_aranges section (as ByteString) into a map from an address range to a debug info id that indexes the DwarfInfo.
parseDwarfAranges :: Bool -> Bool -> B.ByteString -> [([(Word64, Word64)], Word64)]
parseDwarfAranges littleEndian target64 aranges_section =
    let dr = dwarfEndianReader littleEndian
    in runGet (getAddressRangeTable target64 dr) $ L.fromChunks [aranges_section]

-- Section 7.21 - Line Number Information
data DW_LNI
    = DW_LNI_special Word64 Int64
    | DW_LNS_copy
    | DW_LNS_advance_pc Word64
    | DW_LNS_advance_line Int64
    | DW_LNS_set_file Word64
    | DW_LNS_set_column Word64
    | DW_LNS_negate_stmt
    | DW_LNS_set_basic_block
    | DW_LNS_const_add_pc Word64
    | DW_LNS_fixed_advance_pc Word64
    | DW_LNS_set_prologue_end
    | DW_LNS_set_epilogue_begin
    | DW_LNS_set_isa Word64
    | DW_LNE_end_sequence
    | DW_LNE_set_address Word64
    | DW_LNE_define_file String Word64 Word64 Word64
    deriving (Show, Eq)
getDW_LNI dr line_base line_range opcode_base minimum_instruction_length = liftM fromIntegral getWord8 >>= getDW_LNI_
    where getDW_LNI_ 0x00 = do
            length <- liftM fromIntegral getULEB128
            rest   <- getByteString length
            return $ runGet getDW_LNE $ L.fromChunks [rest]
                where getDW_LNE = getWord8 >>= getDW_LNE_
                      getDW_LNE_ 0x01 = return DW_LNE_end_sequence
                      getDW_LNE_ 0x02 = return DW_LNE_set_address <*> getDwarfTargetAddress dr
                      getDW_LNE_ 0x03 = return DW_LNE_define_file <*> getNullTerminatedString <*> getULEB128 <*> getULEB128 <*> getULEB128
                      getDW_LNE_ n | 0x80 <= n && n <= 0xff = fail $ "User DW_LNE data requires extension of parser for code " ++ show n
                      getDW_LNE_ n = fail $ "Unexpected DW_LNE code " ++ show n
          getDW_LNI_ 0x01 = return DW_LNS_copy
          getDW_LNI_ 0x02 = return DW_LNS_advance_pc <*> liftM (* minimum_instruction_length) getULEB128
          getDW_LNI_ 0x03 = return DW_LNS_advance_line <*> getSLEB128
          getDW_LNI_ 0x04 = return DW_LNS_set_file <*> getULEB128
          getDW_LNI_ 0x05 = return DW_LNS_set_column <*> getULEB128
          getDW_LNI_ 0x06 = return DW_LNS_negate_stmt
          getDW_LNI_ 0x07 = return DW_LNS_set_basic_block
          getDW_LNI_ 0x08 = return $ DW_LNS_const_add_pc (minimum_instruction_length * fromIntegral ((255 - opcode_base) `div` line_range))
          getDW_LNI_ 0x09 = return DW_LNS_fixed_advance_pc <*> liftM fromIntegral (getWord16 dr)
          getDW_LNI_ 0x0a = return DW_LNS_set_prologue_end
          getDW_LNI_ 0x0b = return DW_LNS_set_epilogue_begin
          getDW_LNI_ 0x0c = return DW_LNS_set_isa <*> getULEB128
          getDW_LNI_ n | n >= opcode_base =
            let addr_incr = minimum_instruction_length * fromIntegral ((n - opcode_base) `div` line_range)
                line_incr = line_base + fromIntegral ((n - opcode_base) `mod` line_range)
             in return $ DW_LNI_special addr_incr line_incr
          getDW_LNI_ n = fail $ "Unexpected DW_LNI opcode " ++ show n

stepLineMachine :: Bool -> Word8 -> DW_LNE -> [DW_LNI] -> [DW_LNE]
stepLineMachine _ _ _ [] = []
stepLineMachine is_stmt mil lnm (DW_LNI_special addr_incr line_incr : xs) =
    let row = lnm { lnmAddress = lnmAddress lnm + addr_incr, lnmLine = lnmLine lnm + fromIntegral line_incr }
        new = row { lnmBasicBlock = False, lnmPrologueEnd = False, lnmEpilogueBegin = False }
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_copy : xs) =
    let row = lnm
        new = row { lnmBasicBlock = False, lnmPrologueEnd = False, lnmEpilogueBegin = False }
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_advance_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_advance_line incr : xs) =
    let new = lnm { lnmLine = lnmLine lnm + fromIntegral incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_file file : xs) =
    let new = lnm { lnmFile = file }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_column col : xs) =
    let new = lnm { lnmColumn = col }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_negate_stmt : xs) =
    let new = lnm { lnmStatement = not (lnmStatement lnm) }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_basic_block : xs) =
    let new = lnm { lnmBasicBlock = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_const_add_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_fixed_advance_pc incr : xs) =
    let new = lnm { lnmAddress = lnmAddress lnm + incr }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_prologue_end : xs) =
    let new = lnm { lnmPrologueEnd = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_epilogue_begin : xs) =
    let new = lnm { lnmEpilogueBegin = True }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNS_set_isa isa : xs) =
    let new = lnm { lnmISA = isa }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_end_sequence : xs) =
    let row = lnm { lnmEndSequence = True }
        new = defaultLNE is_stmt (lnmFiles lnm)
    in row : stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_set_address address : xs) =
    let new = lnm { lnmAddress = address }
    in stepLineMachine is_stmt mil new xs
stepLineMachine is_stmt mil lnm (DW_LNE_define_file name dir_index time length : xs) =
    let new = lnm { lnmFiles = (lnmFiles lnm) ++ [(name, dir_index, time, length)] }
    in stepLineMachine is_stmt mil new xs

data DW_LNE = DW_LNE
    { lnmAddress       :: Word64
    , lnmFile          :: Word64
    , lnmLine          :: Word64
    , lnmColumn        :: Word64
    , lnmStatement     :: Bool
    , lnmBasicBlock    :: Bool
    , lnmEndSequence   :: Bool
    , lnmPrologueEnd   :: Bool
    , lnmEpilogueBegin :: Bool
    , lnmISA           :: Word64
    , lnmFiles         :: [(String, Word64, Word64, Word64)]
    } deriving (Show, Eq)
defaultLNE is_stmt files = DW_LNE
    { lnmAddress       = 0
    , lnmFile          = 1
    , lnmLine          = 1
    , lnmColumn        = 0
    , lnmStatement     = is_stmt
    , lnmBasicBlock    = False
    , lnmEndSequence   = False
    , lnmPrologueEnd   = False
    , lnmEpilogueBegin = False
    , lnmISA           = 0
    , lnmFiles         = []
    }

getDebugLineFileNames = do
    file_name <- getNullTerminatedString
    if file_name == [] then
        return []
     else do
        dir_index   <- getULEB128
        last_mod    <- getULEB128
        file_length <- getULEB128
        liftM2 (:) (return (file_name, dir_index, last_mod, file_length)) getDebugLineFileNames

-- | Retrieves the line information for a DIE from a given substring of the .debug_line section. The offset
-- into the .debug_line section is obtained from the DW_AT_stmt_list attribute of a DIE.
parseDwarfLine :: Bool -> Bool -> B.ByteString -> ([String], [DW_LNE])
parseDwarfLine littleEndian target64 bs =
    let dr = dwarfEndianReader littleEndian
    in runGet (getDwarfLine target64 dr) (L.fromChunks [bs])
getDwarfLine target64 dr = do
    let getWhileInclusive cond get = do
        el <- get
        if cond el then
            liftM (el :) $ getWhileInclusive cond get
         else
            return [el]
    (dr, sectLen)              <- getDwarfUnitLength dr
    startLen <- bytesRead
    dr                         <- return $ dwarfReader target64 dr
    version                    <- getWord16 dr
    header_length              <- getDwarfOffset dr
    minimum_instruction_length <- getWord8
    default_is_stmt            <- liftM (/= 0) getWord8
    line_base                  <- get :: Get Int8
    line_range                 <- getWord8
    opcode_base                <- getWord8
    standard_opcode_lengths    <- replicateM (fromIntegral opcode_base - 2) getWord8
    include_directories        <- getWhile (/= "") getNullTerminatedString
    file_names                 <- getDebugLineFileNames
    endLen <- bytesRead
    -- Check if we have reached the end of the section.
    if fromIntegral sectLen <= endLen - startLen
      then return (map (\(name, _, _, _) -> name) file_names, [])
      else do
        line_program <- getWhileInclusive (/= DW_LNE_end_sequence) $
                           getDW_LNI dr (fromIntegral line_base)
                                        line_range
                                        opcode_base
                                        (fromIntegral minimum_instruction_length)
        let initial_state = defaultLNE default_is_stmt file_names
            line_matrix = stepLineMachine default_is_stmt minimum_instruction_length initial_state line_program
         in return (map (\(name, _, _, _) -> name) file_names, line_matrix)

-- Section 7.21 - Macro Information
data DW_MACINFO
    = DW_MACINFO_define Word64 String     -- ^ Line number and defined symbol with definition
    | DW_MACINFO_undef Word64 String      -- ^ Line number and undefined symbol
    | DW_MACINFO_start_file Word64 Word64 -- ^ Marks start of file with the line where the file was included from and a source file index
    | DW_MACINFO_end_file                 -- ^ Marks end of file
    | DW_MACINFO_vendor_ext Word64 String -- ^ Implementation defined
    deriving (Show, Eq)

-- | Retrieves the macro information for a compilation unit from a given substring of the .debug_macinfo section. The offset
-- into the .debug_macinfo section is obtained from the DW_AT_macro_info attribute of a compilation unit DIE.
parseDwarfMacInfo :: B.ByteString -> [DW_MACINFO]
parseDwarfMacInfo bs = runGet getDwarfMacInfo (L.fromChunks [bs])
getDwarfMacInfo = do
    x <- getWord8
    case x of
        0x00 -> return []
        0x01 -> pure (:) <*> (pure DW_MACINFO_define     <*> getULEB128 <*> getNullTerminatedString) <*> getDwarfMacInfo
        0x02 -> pure (:) <*> (pure DW_MACINFO_undef      <*> getULEB128 <*> getNullTerminatedString) <*> getDwarfMacInfo
        0x03 -> pure (:) <*> (pure DW_MACINFO_start_file <*> getULEB128 <*> getULEB128)              <*> getDwarfMacInfo
        0x04 -> pure (:) <*> (pure DW_MACINFO_end_file)                                              <*> getDwarfMacInfo
        0xff -> pure (:) <*> (pure DW_MACINFO_vendor_ext <*> getULEB128 <*> getNullTerminatedString) <*> getDwarfMacInfo

-- Section 7.22 - Call Frame
data DW_CFA
    = DW_CFA_advance_loc Word8
    | DW_CFA_offset Word8 Word64
    | DW_CFA_restore Word8
    | DW_CFA_nop
    | DW_CFA_set_loc Word64
    | DW_CFA_advance_loc1 Word8
    | DW_CFA_advance_loc2 Word16
    | DW_CFA_advance_loc4 Word32
    | DW_CFA_offset_extended Word64 Word64
    | DW_CFA_restore_extended Word64
    | DW_CFA_undefined Word64
    | DW_CFA_same_value Word64
    | DW_CFA_register Word64 Word64
    | DW_CFA_remember_state
    | DW_CFA_restore_state
    | DW_CFA_def_cfa Word64 Word64
    | DW_CFA_def_cfa_register Word64
    | DW_CFA_def_cfa_offset Word64
    | DW_CFA_def_cfa_expression B.ByteString
    | DW_CFA_expression Word64 B.ByteString
    | DW_CFA_offset_extended_sf Word64 Int64
    | DW_CFA_def_cfa_sf Word64 Int64
    | DW_CFA_def_cfa_offset_sf Int64
    | DW_CFA_val_offset Word64 Word64
    | DW_CFA_val_offset_sf Word64 Int64
    | DW_CFA_val_expression Word64 B.ByteString
    deriving (Show, Eq)
getDW_CFA dr = do
    tag <- getWord8
    case tag `shiftR` 6 of
        0x1 -> return $ DW_CFA_advance_loc $ tag .&. 0x3f
        0x2 -> return (DW_CFA_offset (tag .&. 0x3f)) <*> getULEB128
        0x3 -> return $ DW_CFA_restore $ tag .&. 0x3f
        0x0 -> case tag .&. 0x3f of
            0x00 -> return DW_CFA_nop
            0x01 -> return DW_CFA_set_loc <*> getDwarfTargetAddress dr
            0x02 -> return DW_CFA_advance_loc1 <*> getWord8
            0x03 -> return DW_CFA_advance_loc2 <*> getWord16 dr
            0x04 -> return DW_CFA_advance_loc4 <*> getWord32 dr
            0x05 -> return DW_CFA_offset_extended <*> getULEB128 <*> getULEB128
            0x06 -> return DW_CFA_restore_extended <*> getULEB128
            0x07 -> return DW_CFA_undefined <*> getULEB128
            0x08 -> return DW_CFA_same_value <*> getULEB128
            0x09 -> return DW_CFA_register <*> getULEB128 <*> getULEB128
            0x0a -> return DW_CFA_remember_state
            0x0b -> return DW_CFA_restore_state
            0x0c -> return DW_CFA_def_cfa <*> getULEB128 <*> getULEB128
            0x0d -> return DW_CFA_def_cfa_register <*> getULEB128
            0x0e -> return DW_CFA_def_cfa_offset <*> getULEB128
            0x0f -> return DW_CFA_def_cfa_expression <*> (liftM fromIntegral getULEB128 >>= getByteString)
            0x10 -> return DW_CFA_expression <*> getULEB128 <*> (liftM fromIntegral getULEB128 >>= getByteString)
            0x11 -> return DW_CFA_offset_extended_sf <*> getULEB128 <*> getSLEB128
            0x12 -> return DW_CFA_def_cfa_sf <*> getULEB128 <*> getSLEB128
            0x13 -> return DW_CFA_def_cfa_offset_sf <*> getSLEB128
            0x14 -> return DW_CFA_val_offset <*> getULEB128 <*> getULEB128
            0x15 -> return DW_CFA_val_offset_sf <*> getULEB128 <*> getSLEB128
            0x16 -> return DW_CFA_val_expression <*> getULEB128 <*> (liftM fromIntegral getULEB128 >>= getByteString)

data DW_CIEFDE
    = DW_CIE
        { cieAugmentation          :: String
        , cieCodeAlignmentFactor   :: Word64
        , cieDataAlignmentFactor   :: Int64
        , cieReturnAddressRegister :: Word64
        , cieInitialInstructions   :: [DW_CFA]
        }
    | DW_FDE
        { fdeCiePointer      :: Word64
        , fdeInitialLocation :: Word64
        , fdeAddressRange    :: Word64
        , fdeInstructions    :: [DW_CFA]
        }
    deriving (Show, Eq)

getWhileNotEmpty :: Get a -> Get [a]
getWhileNotEmpty get = do
    empty <- isEmpty
    if empty then
        return []
     else do
        liftM2 (:) get (getWhileNotEmpty get)

getCIEFDE littleEndian target64 = do
    dr           <- return $ dwarfEndianReader littleEndian
    (dr, length) <- getDwarfUnitLength dr
    dr           <- return $ dwarfReader target64 dr
    begin        <- bytesRead
    cie_id       <- getDwarfOffset dr
    if cie_id == largestOffset dr then do
        version                 <- getWord8
        augmentation            <- getNullTerminatedString
        code_alignment_factor   <- getULEB128
        data_alignment_factor   <- getSLEB128
        return_address_register <- case version of
                                    1 -> liftM fromIntegral $ getWord8
                                    3 -> getULEB128
                                    n -> fail $ "Unrecognized CIE version " ++ show n
        end                     <- bytesRead
        raw_instructions        <- getByteString $ fromIntegral (fromIntegral length - (end - begin))
        initial_instructions    <- return $ runGet (getWhileNotEmpty (getDW_CFA dr)) $ L.fromChunks [raw_instructions]
        return $ DW_CIE augmentation code_alignment_factor data_alignment_factor return_address_register initial_instructions
     else do
        initial_location        <- getDwarfTargetAddress dr
        address_range           <- getDwarfTargetAddress dr
        end                     <- bytesRead
        raw_instructions        <- getByteString $ fromIntegral (fromIntegral length - (end - begin))
        instructions            <- return $ runGet (getWhileNotEmpty (getDW_CFA dr)) $ L.fromChunks [raw_instructions]
        return $ DW_FDE cie_id initial_location address_range instructions

-- | Parse the .debug_frame section into a list of DW_CIEFDE records.
parseDwarfFrame :: Bool         -- ^ True for little endian data. False for big endian.
                -> Bool         -- ^ True for 64-bit target addresses. False of 32-bit target addresses.
                -> B.ByteString -- ^ ByteString for the .debug_frame section.
                -> [DW_CIEFDE]
parseDwarfFrame littleEndian target64 bs = runGet (getWhileNotEmpty $ getCIEFDE littleEndian target64) (L.fromChunks [bs])

-- Section 7.23 - Non-contiguous Address Ranges
-- | Retrieves the non-contiguous address ranges for a compilation unit from a given substring of the .debug_ranges section. The offset
-- into the .debug_ranges section is obtained from the DW_AT_ranges attribute of a compilation unit DIE.
-- Left results are base address entries. Right results are address ranges.
parseDwarfRanges :: DwarfReader -> B.ByteString -> [Either Word64 (Word64, Word64)]
parseDwarfRanges dr bs = runGet (getDwarfRanges dr) (L.fromChunks [bs])
getDwarfRanges dr = do
    begin <- getDwarfTargetAddress dr
    end   <- getDwarfTargetAddress dr
    if begin == 0 && end == 0 then
        return []
     else if begin == largestTargetAddress dr then
        return (Left end :) <*> getDwarfRanges dr
     else
        return (Right (begin, end) :) <*> getDwarfRanges dr

-- Section 7.7.3
-- | Retrieves the location list expressions from a given substring of the .debug_loc section. The offset
-- into the .debug_loc section is obtained from an attribute of class loclistptr for a given DIE.
-- Left results are base address entries. Right results are address ranges and a location expression.
parseDwarfLoc :: DwarfReader -> B.ByteString -> [Either Word64 (Word64, Word64, B.ByteString)]
parseDwarfLoc dr bs = runGet (getDwarfLoc dr) (L.fromChunks [bs])
getDwarfLoc dr = do
    begin <- getDwarfTargetAddress dr
    end   <- getDwarfTargetAddress dr
    if begin == 0 && end == 0 then
        return []
     else if begin == largestTargetAddress dr then
        return (Left end :) <*> getDwarfLoc dr
      else do
        len  <- liftM fromIntegral (getWord16 dr)
        expr <- getByteString len
        return (Right (begin, end, expr) :) <*> getDwarfLoc dr

data DW_TAG
    = DW_TAG_array_type
    | DW_TAG_class_type
    | DW_TAG_entry_point
    | DW_TAG_enumeration_type
    | DW_TAG_formal_parameter
    | DW_TAG_imported_declaration
    | DW_TAG_label
    | DW_TAG_lexical_block
    | DW_TAG_member
    | DW_TAG_pointer_type
    | DW_TAG_reference_type
    | DW_TAG_compile_unit
    | DW_TAG_string_type
    | DW_TAG_structure_type
    | DW_TAG_subroutine_type
    | DW_TAG_typedef
    | DW_TAG_union_type
    | DW_TAG_unspecified_parameters
    | DW_TAG_variant
    | DW_TAG_common_block
    | DW_TAG_common_inclusion
    | DW_TAG_inheritance
    | DW_TAG_inlined_subroutine
    | DW_TAG_module
    | DW_TAG_ptr_to_member_type
    | DW_TAG_set_type
    | DW_TAG_subrange_type
    | DW_TAG_with_stmt
    | DW_TAG_access_declaration
    | DW_TAG_base_type
    | DW_TAG_catch_block
    | DW_TAG_const_type
    | DW_TAG_constant
    | DW_TAG_enumerator
    | DW_TAG_file_type
    | DW_TAG_friend
    | DW_TAG_namelist
    | DW_TAG_namelist_item
    | DW_TAG_packed_type
    | DW_TAG_subprogram
    | DW_TAG_template_type_parameter
    | DW_TAG_template_value_parameter
    | DW_TAG_thrown_type
    | DW_TAG_try_block
    | DW_TAG_variant_part
    | DW_TAG_variable
    | DW_TAG_volatile_type
    | DW_TAG_dwarf_procedure
    | DW_TAG_restrict_type
    | DW_TAG_interface_type
    | DW_TAG_namespace
    | DW_TAG_imported_module
    | DW_TAG_unspecified_type
    | DW_TAG_partial_unit
    | DW_TAG_imported_unit
    | DW_TAG_condition
    | DW_TAG_shared_type
    deriving (Show, Eq)
getDW_TAG = getULEB128 >>= dw_tag
    where dw_tag 0x01 = return DW_TAG_array_type
          dw_tag 0x02 = return DW_TAG_class_type
          dw_tag 0x03 = return DW_TAG_entry_point
          dw_tag 0x04 = return DW_TAG_enumeration_type
          dw_tag 0x05 = return DW_TAG_formal_parameter
          dw_tag 0x08 = return DW_TAG_imported_declaration
          dw_tag 0x0a = return DW_TAG_label
          dw_tag 0x0b = return DW_TAG_lexical_block
          dw_tag 0x0d = return DW_TAG_member
          dw_tag 0x0f = return DW_TAG_pointer_type
          dw_tag 0x10 = return DW_TAG_reference_type
          dw_tag 0x11 = return DW_TAG_compile_unit
          dw_tag 0x12 = return DW_TAG_string_type
          dw_tag 0x13 = return DW_TAG_structure_type
          dw_tag 0x15 = return DW_TAG_subroutine_type
          dw_tag 0x16 = return DW_TAG_typedef
          dw_tag 0x17 = return DW_TAG_union_type
          dw_tag 0x18 = return DW_TAG_unspecified_parameters
          dw_tag 0x19 = return DW_TAG_variant
          dw_tag 0x1a = return DW_TAG_common_block
          dw_tag 0x1b = return DW_TAG_common_inclusion
          dw_tag 0x1c = return DW_TAG_inheritance
          dw_tag 0x1d = return DW_TAG_inlined_subroutine
          dw_tag 0x1e = return DW_TAG_module
          dw_tag 0x1f = return DW_TAG_ptr_to_member_type
          dw_tag 0x20 = return DW_TAG_set_type
          dw_tag 0x21 = return DW_TAG_subrange_type
          dw_tag 0x22 = return DW_TAG_with_stmt
          dw_tag 0x23 = return DW_TAG_access_declaration
          dw_tag 0x24 = return DW_TAG_base_type
          dw_tag 0x25 = return DW_TAG_catch_block
          dw_tag 0x26 = return DW_TAG_const_type
          dw_tag 0x27 = return DW_TAG_constant
          dw_tag 0x28 = return DW_TAG_enumerator
          dw_tag 0x29 = return DW_TAG_file_type
          dw_tag 0x2a = return DW_TAG_friend
          dw_tag 0x2b = return DW_TAG_namelist
          dw_tag 0x2c = return DW_TAG_namelist_item
          dw_tag 0x2d = return DW_TAG_packed_type
          dw_tag 0x2e = return DW_TAG_subprogram
          dw_tag 0x2f = return DW_TAG_template_type_parameter
          dw_tag 0x30 = return DW_TAG_template_value_parameter
          dw_tag 0x31 = return DW_TAG_thrown_type
          dw_tag 0x32 = return DW_TAG_try_block
          dw_tag 0x33 = return DW_TAG_variant_part
          dw_tag 0x34 = return DW_TAG_variable
          dw_tag 0x35 = return DW_TAG_volatile_type
          dw_tag 0x36 = return DW_TAG_dwarf_procedure
          dw_tag 0x37 = return DW_TAG_restrict_type
          dw_tag 0x38 = return DW_TAG_interface_type
          dw_tag 0x39 = return DW_TAG_namespace
          dw_tag 0x3a = return DW_TAG_imported_module
          dw_tag 0x3b = return DW_TAG_unspecified_type
          dw_tag 0x3c = return DW_TAG_partial_unit
          dw_tag 0x3d = return DW_TAG_imported_unit
          dw_tag 0x3f = return DW_TAG_condition
          dw_tag 0x40 = return DW_TAG_shared_type
          dw_tag n | 0x4080 <= n && n <= 0xffff = fail $ "User DW_TAG data requires extension of parser for code " ++ show n
          dw_tag n = fail $ "Unrecognized DW_TAG " ++ show n

data DW_AT
    = DW_AT_sibling              -- ^ reference
    | DW_AT_location             -- ^ block, loclistptr
    | DW_AT_name                 -- ^ string
    | DW_AT_ordering             -- ^ constant
    | DW_AT_byte_size            -- ^ block, constant, reference
    | DW_AT_bit_offset           -- ^ block, constant, reference
    | DW_AT_bit_size             -- ^ block, constant, reference
    | DW_AT_stmt_list            -- ^ lineptr
    | DW_AT_low_pc               -- ^ address
    | DW_AT_high_pc              -- ^ address
    | DW_AT_language             -- ^ constant
    | DW_AT_discr                -- ^ reference
    | DW_AT_discr_value          -- ^ constant
    | DW_AT_visibility           -- ^ constant
    | DW_AT_import               -- ^ reference
    | DW_AT_string_length        -- ^ block, loclistptr
    | DW_AT_common_reference     -- ^ reference
    | DW_AT_comp_dir             -- ^ string
    | DW_AT_const_value          -- ^ block, constant, string
    | DW_AT_containing_type      -- ^ reference
    | DW_AT_default_value        -- ^ reference
    | DW_AT_inline               -- ^ constant
    | DW_AT_is_optional          -- ^ flag
    | DW_AT_lower_bound          -- ^ block, constant, reference
    | DW_AT_producer             -- ^ string
    | DW_AT_prototyped           -- ^ flag
    | DW_AT_return_addr          -- ^ block, loclistptr
    | DW_AT_start_scope          -- ^ constant
    | DW_AT_bit_stride           -- ^ constant
    | DW_AT_upper_bound          -- ^ block, constant, reference
    | DW_AT_abstract_origin      -- ^ reference
    | DW_AT_accessibility        -- ^ constant
    | DW_AT_address_class        -- ^ constant
    | DW_AT_artificial           -- ^ flag
    | DW_AT_base_types           -- ^ reference
    | DW_AT_calling_convention   -- ^ constant
    | DW_AT_count                -- ^ block, constant, reference
    | DW_AT_data_member_location -- ^ block, constant, loclistptr
    | DW_AT_decl_column          -- ^ constant
    | DW_AT_decl_file            -- ^ constant
    | DW_AT_decl_line            -- ^ constant
    | DW_AT_declaration          -- ^ flag
    | DW_AT_discr_list           -- ^ block
    | DW_AT_encoding             -- ^ constant
    | DW_AT_external             -- ^ flag
    | DW_AT_frame_base           -- ^ block, loclistptr
    | DW_AT_friend               -- ^ reference
    | DW_AT_identifier_case      -- ^ constant
    | DW_AT_macro_info           -- ^ macptr
    | DW_AT_namelist_item        -- ^ block
    | DW_AT_priority             -- ^ reference
    | DW_AT_segment              -- ^ block, loclistptr
    | DW_AT_specification        -- ^ reference
    | DW_AT_static_link          -- ^ block, loclistptr
    | DW_AT_type                 -- ^ reference
    | DW_AT_use_location         -- ^ block, loclistptr
    | DW_AT_variable_parameter   -- ^ flag
    | DW_AT_virtuality           -- ^ constant
    | DW_AT_vtable_elem_location -- ^ block, loclistptr
    | DW_AT_allocated            -- ^ block, constant, reference
    | DW_AT_associated           -- ^ block, constant, reference
    | DW_AT_data_location        -- ^ block
    | DW_AT_byte_stride          -- ^ block, constant, reference
    | DW_AT_entry_pc             -- ^ address
    | DW_AT_use_UTF8             -- ^ flag
    | DW_AT_extension            -- ^ reference
    | DW_AT_ranges               -- ^ rangelistptr
    | DW_AT_trampoline           -- ^ address, flag, reference, string
    | DW_AT_call_column          -- ^ constant
    | DW_AT_call_file            -- ^ constant
    | DW_AT_call_line            -- ^ constant
    | DW_AT_description          -- ^ string
    | DW_AT_binary_scale         -- ^ constant
    | DW_AT_decimal_scale        -- ^ constant
    | DW_AT_small                -- ^ reference
    | DW_AT_decimal_sign         -- ^ constant
    | DW_AT_digit_count          -- ^ constant
    | DW_AT_picture_string       -- ^ string
    | DW_AT_mutable              -- ^ flag
    | DW_AT_threads_scaled       -- ^ flag
    | DW_AT_explicit             -- ^ flag
    | DW_AT_object_pointer       -- ^ reference
    | DW_AT_endianity            -- ^ constant
    | DW_AT_elemental            -- ^ flag
    | DW_AT_pure                 -- ^ flag
    | DW_AT_recursive            -- ^ flag
    | DW_AT_user Word64          -- ^ user extension
    deriving (Show, Eq)
dw_at 0x01 = DW_AT_sibling
dw_at 0x02 = DW_AT_location
dw_at 0x03 = DW_AT_name
dw_at 0x09 = DW_AT_ordering
dw_at 0x0b = DW_AT_byte_size
dw_at 0x0c = DW_AT_bit_offset
dw_at 0x0d = DW_AT_bit_size
dw_at 0x10 = DW_AT_stmt_list
dw_at 0x11 = DW_AT_low_pc
dw_at 0x12 = DW_AT_high_pc
dw_at 0x13 = DW_AT_language
dw_at 0x15 = DW_AT_discr
dw_at 0x16 = DW_AT_discr_value
dw_at 0x17 = DW_AT_visibility
dw_at 0x18 = DW_AT_import
dw_at 0x19 = DW_AT_string_length
dw_at 0x1a = DW_AT_common_reference
dw_at 0x1b = DW_AT_comp_dir
dw_at 0x1c = DW_AT_const_value
dw_at 0x1d = DW_AT_containing_type
dw_at 0x1e = DW_AT_default_value
dw_at 0x20 = DW_AT_inline
dw_at 0x21 = DW_AT_is_optional
dw_at 0x22 = DW_AT_lower_bound
dw_at 0x25 = DW_AT_producer
dw_at 0x27 = DW_AT_prototyped
dw_at 0x2a = DW_AT_return_addr
dw_at 0x2c = DW_AT_start_scope
dw_at 0x2e = DW_AT_bit_stride
dw_at 0x2f = DW_AT_upper_bound
dw_at 0x31 = DW_AT_abstract_origin
dw_at 0x32 = DW_AT_accessibility
dw_at 0x33 = DW_AT_address_class
dw_at 0x34 = DW_AT_artificial
dw_at 0x35 = DW_AT_base_types
dw_at 0x36 = DW_AT_calling_convention
dw_at 0x37 = DW_AT_count
dw_at 0x38 = DW_AT_data_member_location
dw_at 0x39 = DW_AT_decl_column
dw_at 0x3a = DW_AT_decl_file
dw_at 0x3b = DW_AT_decl_line
dw_at 0x3c = DW_AT_declaration
dw_at 0x3d = DW_AT_discr_list
dw_at 0x3e = DW_AT_encoding
dw_at 0x3f = DW_AT_external
dw_at 0x40 = DW_AT_frame_base
dw_at 0x41 = DW_AT_friend
dw_at 0x42 = DW_AT_identifier_case
dw_at 0x43 = DW_AT_macro_info
dw_at 0x44 = DW_AT_namelist_item
dw_at 0x45 = DW_AT_priority
dw_at 0x46 = DW_AT_segment
dw_at 0x47 = DW_AT_specification
dw_at 0x48 = DW_AT_static_link
dw_at 0x49 = DW_AT_type
dw_at 0x4a = DW_AT_use_location
dw_at 0x4b = DW_AT_variable_parameter
dw_at 0x4c = DW_AT_virtuality
dw_at 0x4d = DW_AT_vtable_elem_location
dw_at 0x4e = DW_AT_allocated
dw_at 0x4f = DW_AT_associated
dw_at 0x50 = DW_AT_data_location
dw_at 0x51 = DW_AT_byte_stride
dw_at 0x52 = DW_AT_entry_pc
dw_at 0x53 = DW_AT_use_UTF8
dw_at 0x54 = DW_AT_extension
dw_at 0x55 = DW_AT_ranges
dw_at 0x56 = DW_AT_trampoline
dw_at 0x57 = DW_AT_call_column
dw_at 0x58 = DW_AT_call_file
dw_at 0x59 = DW_AT_call_line
dw_at 0x5a = DW_AT_description
dw_at 0x5b = DW_AT_binary_scale
dw_at 0x5c = DW_AT_decimal_scale
dw_at 0x5d = DW_AT_small
dw_at 0x5e = DW_AT_decimal_sign
dw_at 0x5f = DW_AT_digit_count
dw_at 0x60 = DW_AT_picture_string
dw_at 0x61 = DW_AT_mutable
dw_at 0x62 = DW_AT_threads_scaled
dw_at 0x63 = DW_AT_explicit
dw_at 0x64 = DW_AT_object_pointer
dw_at 0x65 = DW_AT_endianity
dw_at 0x66 = DW_AT_elemental
dw_at 0x67 = DW_AT_pure
dw_at 0x68 = DW_AT_recursive
dw_at n | 0x2000 <= n && n <= 0x3fff = DW_AT_user n 
dw_at n = error $ "Unrecognized DW_AT " ++ show n

data DW_ATVAL
    = DW_ATVAL_INT    Int64
    | DW_ATVAL_UINT   Word64
    | DW_ATVAL_STRING String
    | DW_ATVAL_BLOB   B.ByteString
    | DW_ATVAL_BOOL   Bool
    deriving (Show, Eq)

data DW_FORM
    = DW_FORM_addr              -- ^ address
    | DW_FORM_block2 -- ^ block
    | DW_FORM_block4 -- ^ block
    | DW_FORM_data2 -- ^ constant
    | DW_FORM_data4 -- ^ constant, lineptr, loclistptr, macptr, rangelistptr
    | DW_FORM_data8 -- ^ constant, lineptr, loclistptr, macptr, rangelistptr
    | DW_FORM_string -- ^ string
    | DW_FORM_block -- ^ block
    | DW_FORM_block1 -- ^ block
    | DW_FORM_data1 -- ^ constant
    | DW_FORM_flag -- ^ flag
    | DW_FORM_sdata -- ^ constant
    | DW_FORM_strp -- ^ string
    | DW_FORM_udata -- ^ constant
    | DW_FORM_ref_addr            -- ^ reference
    | DW_FORM_ref1                -- ^ reference
    | DW_FORM_ref2                -- ^ reference
    | DW_FORM_ref4                -- ^ reference
    | DW_FORM_ref8                -- ^ reference
    | DW_FORM_ref_udata           -- ^ reference
    | DW_FORM_indirect            -- ^ (see Section 7.5.3 of DWARF3 specification)
    deriving (Show, Eq)
dw_form 0x01 = DW_FORM_addr
dw_form 0x03 = DW_FORM_block2
dw_form 0x04 = DW_FORM_block4
dw_form 0x05 = DW_FORM_data2
dw_form 0x06 = DW_FORM_data4
dw_form 0x07 = DW_FORM_data8
dw_form 0x08 = DW_FORM_string
dw_form 0x09 = DW_FORM_block
dw_form 0x0a = DW_FORM_block1
dw_form 0x0b = DW_FORM_data1
dw_form 0x0c = DW_FORM_flag
dw_form 0x0d = DW_FORM_sdata
dw_form 0x0e = DW_FORM_strp
dw_form 0x0f = DW_FORM_udata
dw_form 0x10 = DW_FORM_ref_addr
dw_form 0x11 = DW_FORM_ref1
dw_form 0x12 = DW_FORM_ref2
dw_form 0x13 = DW_FORM_ref4
dw_form 0x14 = DW_FORM_ref8
dw_form 0x15 = DW_FORM_ref_udata
dw_form 0x16 = DW_FORM_indirect
dw_form n    = error $ "Unrecognized DW_FORM " ++ show n

data DW_OP
    = DW_OP_addr Word64
    | DW_OP_deref
    | DW_OP_const1u Word8
    | DW_OP_const1s Int8
    | DW_OP_const2u Word16
    | DW_OP_const2s Int16
    | DW_OP_const4u Word32
    | DW_OP_const4s Int32
    | DW_OP_const8u Word64
    | DW_OP_const8s Int64
    | DW_OP_constu  Word64
    | DW_OP_consts  Int64
    | DW_OP_dup
    | DW_OP_drop
    | DW_OP_over
    | DW_OP_pick Word8
    | DW_OP_swap
    | DW_OP_rot
    | DW_OP_xderef
    | DW_OP_abs
    | DW_OP_and
    | DW_OP_div
    | DW_OP_minus
    | DW_OP_mod
    | DW_OP_mul
    | DW_OP_neg
    | DW_OP_not
    | DW_OP_or
    | DW_OP_plus
    | DW_OP_plus_uconst Word64
    | DW_OP_shl
    | DW_OP_shr
    | DW_OP_shra
    | DW_OP_xor
    | DW_OP_skip Int16
    | DW_OP_bra Int16
    | DW_OP_eq
    | DW_OP_ge
    | DW_OP_gt
    | DW_OP_le
    | DW_OP_lt
    | DW_OP_ne
    | DW_OP_lit0
    | DW_OP_lit1
    | DW_OP_lit2
    | DW_OP_lit3
    | DW_OP_lit4
    | DW_OP_lit5
    | DW_OP_lit6
    | DW_OP_lit7
    | DW_OP_lit8
    | DW_OP_lit9
    | DW_OP_lit10
    | DW_OP_lit11
    | DW_OP_lit12
    | DW_OP_lit13
    | DW_OP_lit14
    | DW_OP_lit15
    | DW_OP_lit16
    | DW_OP_lit17
    | DW_OP_lit18
    | DW_OP_lit19
    | DW_OP_lit20
    | DW_OP_lit21
    | DW_OP_lit22
    | DW_OP_lit23
    | DW_OP_lit24
    | DW_OP_lit25
    | DW_OP_lit26
    | DW_OP_lit27
    | DW_OP_lit28
    | DW_OP_lit29
    | DW_OP_lit30
    | DW_OP_lit31
    | DW_OP_reg0
    | DW_OP_reg1
    | DW_OP_reg2
    | DW_OP_reg3
    | DW_OP_reg4
    | DW_OP_reg5
    | DW_OP_reg6
    | DW_OP_reg7
    | DW_OP_reg8
    | DW_OP_reg9
    | DW_OP_reg10
    | DW_OP_reg11
    | DW_OP_reg12
    | DW_OP_reg13
    | DW_OP_reg14
    | DW_OP_reg15
    | DW_OP_reg16
    | DW_OP_reg17
    | DW_OP_reg18
    | DW_OP_reg19
    | DW_OP_reg20
    | DW_OP_reg21
    | DW_OP_reg22
    | DW_OP_reg23
    | DW_OP_reg24
    | DW_OP_reg25
    | DW_OP_reg26
    | DW_OP_reg27
    | DW_OP_reg28
    | DW_OP_reg29
    | DW_OP_reg30
    | DW_OP_reg31
    | DW_OP_breg0 Int64
    | DW_OP_breg1 Int64
    | DW_OP_breg2 Int64
    | DW_OP_breg3 Int64
    | DW_OP_breg4 Int64
    | DW_OP_breg5 Int64
    | DW_OP_breg6 Int64
    | DW_OP_breg7 Int64
    | DW_OP_breg8 Int64
    | DW_OP_breg9 Int64
    | DW_OP_breg10 Int64
    | DW_OP_breg11 Int64
    | DW_OP_breg12 Int64
    | DW_OP_breg13 Int64
    | DW_OP_breg14 Int64
    | DW_OP_breg15 Int64
    | DW_OP_breg16 Int64
    | DW_OP_breg17 Int64
    | DW_OP_breg18 Int64
    | DW_OP_breg19 Int64
    | DW_OP_breg20 Int64
    | DW_OP_breg21 Int64
    | DW_OP_breg22 Int64
    | DW_OP_breg23 Int64
    | DW_OP_breg24 Int64
    | DW_OP_breg25 Int64
    | DW_OP_breg26 Int64
    | DW_OP_breg27 Int64
    | DW_OP_breg28 Int64
    | DW_OP_breg29 Int64
    | DW_OP_breg30 Int64
    | DW_OP_breg31 Int64
    | DW_OP_regx Word64
    | DW_OP_fbreg Int64
    | DW_OP_bregx Word64 Int64
    | DW_OP_piece Word64
    | DW_OP_deref_size Word8
    | DW_OP_xderef_size Word8
    | DW_OP_nop
    | DW_OP_push_object_address
    | DW_OP_call2 Word16
    | DW_OP_call4 Word32
    | DW_OP_call_ref Word64
    | DW_OP_form_tls_address
    | DW_OP_call_frame_cfa
    | DW_OP_bit_piece Word64 Word64
    deriving (Show, Eq)
-- | Parse a ByteString into a DWARF opcode. This will be needed for further decoding of DIE attributes.
parseDW_OP :: DwarfReader -> B.ByteString -> DW_OP
parseDW_OP dr bs = runGet (getDW_OP dr) (L.fromChunks [bs])
getDW_OP dr = getWord8 >>= getDW_OP_
    where getDW_OP_ 0x03 = return DW_OP_addr <*> getDwarfTargetAddress dr
          getDW_OP_ 0x06 = return DW_OP_deref
          getDW_OP_ 0x08 = return DW_OP_const1u <*> liftM fromIntegral getWord8
          getDW_OP_ 0x09 = return DW_OP_const1s <*> liftM fromIntegral getWord8
          getDW_OP_ 0x0a = return DW_OP_const2u <*> liftM fromIntegral (getWord16 dr)
          getDW_OP_ 0x0b = return DW_OP_const2s <*> liftM fromIntegral (getWord16 dr)
          getDW_OP_ 0x0c = return DW_OP_const4u <*> liftM fromIntegral (getWord32 dr)
          getDW_OP_ 0x0d = return DW_OP_const4s <*> liftM fromIntegral (getWord32 dr)
          getDW_OP_ 0x0e = return DW_OP_const8u <*> getWord64 dr
          getDW_OP_ 0x0f = return DW_OP_const8s <*> liftM fromIntegral (getWord64 dr)
          getDW_OP_ 0x10 = return DW_OP_constu  <*> getULEB128
          getDW_OP_ 0x11 = return DW_OP_consts  <*> getSLEB128
          getDW_OP_ 0x12 = return DW_OP_dup
          getDW_OP_ 0x13 = return DW_OP_drop
          getDW_OP_ 0x14 = return DW_OP_over
          getDW_OP_ 0x15 = return DW_OP_pick <*> getWord8
          getDW_OP_ 0x16 = return DW_OP_swap
          getDW_OP_ 0x17 = return DW_OP_rot
          getDW_OP_ 0x18 = return DW_OP_xderef
          getDW_OP_ 0x19 = return DW_OP_abs
          getDW_OP_ 0x1a = return DW_OP_and
          getDW_OP_ 0x1b = return DW_OP_div
          getDW_OP_ 0x1c = return DW_OP_minus
          getDW_OP_ 0x1d = return DW_OP_mod
          getDW_OP_ 0x1e = return DW_OP_mul
          getDW_OP_ 0x1f = return DW_OP_neg
          getDW_OP_ 0x20 = return DW_OP_not
          getDW_OP_ 0x21 = return DW_OP_or
          getDW_OP_ 0x22 = return DW_OP_plus
          getDW_OP_ 0x23 = return DW_OP_plus_uconst <*> getULEB128
          getDW_OP_ 0x24 = return DW_OP_shl
          getDW_OP_ 0x25 = return DW_OP_shr
          getDW_OP_ 0x26 = return DW_OP_shra
          getDW_OP_ 0x27 = return DW_OP_xor
          getDW_OP_ 0x2f = return DW_OP_skip <*> liftM fromIntegral (getWord16 dr)
          getDW_OP_ 0x28 = return DW_OP_bra  <*> liftM fromIntegral (getWord16 dr)
          getDW_OP_ 0x29 = return DW_OP_eq
          getDW_OP_ 0x2a = return DW_OP_ge
          getDW_OP_ 0x2b = return DW_OP_gt
          getDW_OP_ 0x2c = return DW_OP_le
          getDW_OP_ 0x2d = return DW_OP_lt
          getDW_OP_ 0x2e = return DW_OP_ne
          getDW_OP_ 0x30 = return DW_OP_lit0
          getDW_OP_ 0x31 = return DW_OP_lit1
          getDW_OP_ 0x32 = return DW_OP_lit2
          getDW_OP_ 0x33 = return DW_OP_lit3
          getDW_OP_ 0x34 = return DW_OP_lit4
          getDW_OP_ 0x35 = return DW_OP_lit5
          getDW_OP_ 0x36 = return DW_OP_lit6
          getDW_OP_ 0x37 = return DW_OP_lit7
          getDW_OP_ 0x38 = return DW_OP_lit8
          getDW_OP_ 0x39 = return DW_OP_lit9
          getDW_OP_ 0x3a = return DW_OP_lit10
          getDW_OP_ 0x3b = return DW_OP_lit11
          getDW_OP_ 0x3c = return DW_OP_lit12
          getDW_OP_ 0x3d = return DW_OP_lit13
          getDW_OP_ 0x3e = return DW_OP_lit14
          getDW_OP_ 0x3f = return DW_OP_lit15
          getDW_OP_ 0x40 = return DW_OP_lit16
          getDW_OP_ 0x41 = return DW_OP_lit17
          getDW_OP_ 0x42 = return DW_OP_lit18
          getDW_OP_ 0x43 = return DW_OP_lit19
          getDW_OP_ 0x44 = return DW_OP_lit20
          getDW_OP_ 0x45 = return DW_OP_lit21
          getDW_OP_ 0x46 = return DW_OP_lit22
          getDW_OP_ 0x47 = return DW_OP_lit23
          getDW_OP_ 0x48 = return DW_OP_lit24
          getDW_OP_ 0x49 = return DW_OP_lit25
          getDW_OP_ 0x4a = return DW_OP_lit26
          getDW_OP_ 0x4b = return DW_OP_lit27
          getDW_OP_ 0x4c = return DW_OP_lit28
          getDW_OP_ 0x4d = return DW_OP_lit29
          getDW_OP_ 0x4e = return DW_OP_lit30
          getDW_OP_ 0x4f = return DW_OP_lit31
          getDW_OP_ 0x50 = return DW_OP_reg0
          getDW_OP_ 0x51 = return DW_OP_reg1
          getDW_OP_ 0x52 = return DW_OP_reg2
          getDW_OP_ 0x53 = return DW_OP_reg3
          getDW_OP_ 0x54 = return DW_OP_reg4
          getDW_OP_ 0x55 = return DW_OP_reg5
          getDW_OP_ 0x56 = return DW_OP_reg6
          getDW_OP_ 0x57 = return DW_OP_reg7
          getDW_OP_ 0x58 = return DW_OP_reg8
          getDW_OP_ 0x59 = return DW_OP_reg9
          getDW_OP_ 0x5a = return DW_OP_reg10
          getDW_OP_ 0x5b = return DW_OP_reg11
          getDW_OP_ 0x5c = return DW_OP_reg12
          getDW_OP_ 0x5d = return DW_OP_reg13
          getDW_OP_ 0x5e = return DW_OP_reg14
          getDW_OP_ 0x5f = return DW_OP_reg15
          getDW_OP_ 0x60 = return DW_OP_reg16
          getDW_OP_ 0x61 = return DW_OP_reg17
          getDW_OP_ 0x62 = return DW_OP_reg18
          getDW_OP_ 0x63 = return DW_OP_reg19
          getDW_OP_ 0x64 = return DW_OP_reg20
          getDW_OP_ 0x65 = return DW_OP_reg21
          getDW_OP_ 0x66 = return DW_OP_reg22
          getDW_OP_ 0x67 = return DW_OP_reg23
          getDW_OP_ 0x68 = return DW_OP_reg24
          getDW_OP_ 0x69 = return DW_OP_reg25
          getDW_OP_ 0x6a = return DW_OP_reg26
          getDW_OP_ 0x6b = return DW_OP_reg27
          getDW_OP_ 0x6c = return DW_OP_reg28
          getDW_OP_ 0x6d = return DW_OP_reg29
          getDW_OP_ 0x6e = return DW_OP_reg30
          getDW_OP_ 0x6f = return DW_OP_reg31
          getDW_OP_ 0x70 = return DW_OP_breg0  <*> getSLEB128
          getDW_OP_ 0x71 = return DW_OP_breg1  <*> getSLEB128
          getDW_OP_ 0x72 = return DW_OP_breg2  <*> getSLEB128
          getDW_OP_ 0x73 = return DW_OP_breg3  <*> getSLEB128
          getDW_OP_ 0x74 = return DW_OP_breg4  <*> getSLEB128
          getDW_OP_ 0x75 = return DW_OP_breg5  <*> getSLEB128
          getDW_OP_ 0x76 = return DW_OP_breg6  <*> getSLEB128
          getDW_OP_ 0x77 = return DW_OP_breg7  <*> getSLEB128
          getDW_OP_ 0x78 = return DW_OP_breg8  <*> getSLEB128
          getDW_OP_ 0x79 = return DW_OP_breg9  <*> getSLEB128
          getDW_OP_ 0x7a = return DW_OP_breg10 <*> getSLEB128
          getDW_OP_ 0x7b = return DW_OP_breg11 <*> getSLEB128
          getDW_OP_ 0x7c = return DW_OP_breg12 <*> getSLEB128
          getDW_OP_ 0x7d = return DW_OP_breg13 <*> getSLEB128
          getDW_OP_ 0x7e = return DW_OP_breg14 <*> getSLEB128
          getDW_OP_ 0x7f = return DW_OP_breg15 <*> getSLEB128
          getDW_OP_ 0x80 = return DW_OP_breg16 <*> getSLEB128
          getDW_OP_ 0x81 = return DW_OP_breg17 <*> getSLEB128
          getDW_OP_ 0x82 = return DW_OP_breg18 <*> getSLEB128
          getDW_OP_ 0x83 = return DW_OP_breg19 <*> getSLEB128
          getDW_OP_ 0x84 = return DW_OP_breg20 <*> getSLEB128
          getDW_OP_ 0x85 = return DW_OP_breg21 <*> getSLEB128
          getDW_OP_ 0x86 = return DW_OP_breg22 <*> getSLEB128
          getDW_OP_ 0x87 = return DW_OP_breg23 <*> getSLEB128
          getDW_OP_ 0x88 = return DW_OP_breg24 <*> getSLEB128
          getDW_OP_ 0x89 = return DW_OP_breg25 <*> getSLEB128
          getDW_OP_ 0x8a = return DW_OP_breg26 <*> getSLEB128
          getDW_OP_ 0x8b = return DW_OP_breg27 <*> getSLEB128
          getDW_OP_ 0x8c = return DW_OP_breg28 <*> getSLEB128
          getDW_OP_ 0x8d = return DW_OP_breg29 <*> getSLEB128
          getDW_OP_ 0x8e = return DW_OP_breg30 <*> getSLEB128
          getDW_OP_ 0x8f = return DW_OP_breg31 <*> getSLEB128
          getDW_OP_ 0x90 = return DW_OP_regx   <*> getULEB128
          getDW_OP_ 0x91 = return DW_OP_fbreg  <*> getSLEB128
          getDW_OP_ 0x92 = return DW_OP_bregx  <*> getULEB128 <*> getSLEB128
          getDW_OP_ 0x93 = return DW_OP_piece  <*> getULEB128
          getDW_OP_ 0x94 = return DW_OP_deref_size <*> getWord8
          getDW_OP_ 0x95 = return DW_OP_xderef_size <*> getWord8
          getDW_OP_ 0x96 = return DW_OP_nop
          getDW_OP_ 0x97 = return DW_OP_push_object_address
          getDW_OP_ 0x98 = return DW_OP_call2 <*> getWord16 dr
          getDW_OP_ 0x99 = return DW_OP_call4 <*> getWord32 dr
          getDW_OP_ 0x9a = return DW_OP_call_ref <*> getDwarfTargetAddress dr
          getDW_OP_ 0x9b = return DW_OP_form_tls_address
          getDW_OP_ 0x9c = return DW_OP_call_frame_cfa
          getDW_OP_ 0x9d = return DW_OP_bit_piece <*> getULEB128 <*> getULEB128
          getDW_OP_ n | 0xe0 <= n && n <= 0xff = fail $ "User DW_OP data requires extension of parser for code " ++ show n
          getDW_OP_ n = fail $ "Unrecognized DW_OP code " ++ show n

data DW_ATE
    = DW_ATE_address
    | DW_ATE_boolean
    | DW_ATE_complex_float
    | DW_ATE_float
    | DW_ATE_signed
    | DW_ATE_signed_char
    | DW_ATE_unsigned
    | DW_ATE_unsigned_char
    | DW_ATE_imaginary_float
    | DW_ATE_packed_decimal
    | DW_ATE_numeric_string
    | DW_ATE_edited
    | DW_ATE_signed_fixed
    | DW_ATE_unsigned_fixed
    | DW_ATE_decimal_float
    deriving (Show, Eq)
dw_ate 0x01 = DW_ATE_address
dw_ate 0x02 = DW_ATE_boolean
dw_ate 0x03 = DW_ATE_complex_float
dw_ate 0x04 = DW_ATE_float
dw_ate 0x05 = DW_ATE_signed
dw_ate 0x06 = DW_ATE_signed_char
dw_ate 0x07 = DW_ATE_unsigned
dw_ate 0x08 = DW_ATE_unsigned_char
dw_ate 0x09 = DW_ATE_imaginary_float
dw_ate 0x0a = DW_ATE_packed_decimal
dw_ate 0x0b = DW_ATE_numeric_string
dw_ate 0x0c = DW_ATE_edited
dw_ate 0x0d = DW_ATE_signed_fixed
dw_ate 0x0e = DW_ATE_unsigned_fixed
dw_ate 0x0f = DW_ATE_decimal_float
dw_ate n = error $ "Unrecognized DW_ATE encoding " ++ show n

data DW_DS
    = DW_DS_unsigned
    | DW_DS_leading_overpunch
    | DW_DS_trailing_overpunch
    | DW_DS_leading_separate
    | DW_DS_trailing_separate
    deriving (Show, Eq)
dw_ds 0x01 = DW_DS_unsigned
dw_ds 0x02 = DW_DS_leading_overpunch
dw_ds 0x03 = DW_DS_trailing_overpunch
dw_ds 0x04 = DW_DS_leading_separate
dw_ds 0x05 = DW_DS_trailing_separate

data DW_END
    = DW_END_default
    | DW_END_big
    | DW_END_little
    deriving (Show, Eq)
dw_end 0x00 = DW_END_default
dw_end 0x01 = DW_END_big
dw_end 0x02 = DW_END_little
dw_end n = error $ "Unrecognized DW_END value " ++ show n

data DW_ACCESS
    = DW_ACCESS_public
    | DW_ACCESS_protected
    | DW_ACCESS_private
    deriving (Show, Eq)
dw_access 0x01 = DW_ACCESS_public
dw_access 0x02 = DW_ACCESS_protected
dw_access 0x03 = DW_ACCESS_private

data DW_VIS
    = DW_VIS_local
    | DW_VIS_exported
    | DW_VIS_qualified
    deriving (Show, Eq)
dw_vis 0x01 = DW_VIS_local
dw_vis 0x02 = DW_VIS_exported
dw_vis 0x03 = DW_VIS_qualified

data DW_VIRTUALITY
    = DW_VIRTUALITY_none
    | DW_VIRTUALITY_virtual
    | DW_VIRTUALITY_pure_virtual
    deriving (Show, Eq)
dw_virtuality 0x00 = DW_VIRTUALITY_none
dw_virtuality 0x01 = DW_VIRTUALITY_virtual
dw_virtuality 0x02 = DW_VIRTUALITY_pure_virtual

data DW_LANG
    = DW_LANG_C89
    | DW_LANG_C
    | DW_LANG_Ada83
    | DW_LANG_C_plus_plus
    | DW_LANG_Cobol74
    | DW_LANG_Cobol85
    | DW_LANG_Fortran77
    | DW_LANG_Fortran90
    | DW_LANG_Pascal83
    | DW_LANG_Modula2
    | DW_LANG_Java
    | DW_LANG_C99
    | DW_LANG_Ada95
    | DW_LANG_Fortran95
    | DW_LANG_PLI
    | DW_LANG_ObjC
    | DW_LANG_ObjC_plus_plus
    | DW_LANG_UPC
    | DW_LANG_D
    deriving (Show, Eq)
dw_lang 0x0001 = DW_LANG_C89
dw_lang 0x0002 = DW_LANG_C
dw_lang 0x0003 = DW_LANG_Ada83
dw_lang 0x0004 = DW_LANG_C_plus_plus
dw_lang 0x0005 = DW_LANG_Cobol74
dw_lang 0x0006 = DW_LANG_Cobol85
dw_lang 0x0007 = DW_LANG_Fortran77
dw_lang 0x0008 = DW_LANG_Fortran90
dw_lang 0x0009 = DW_LANG_Pascal83
dw_lang 0x000a = DW_LANG_Modula2
dw_lang 0x000b = DW_LANG_Java
dw_lang 0x000c = DW_LANG_C99
dw_lang 0x000d = DW_LANG_Ada95
dw_lang 0x000e = DW_LANG_Fortran95
dw_lang 0x000f = DW_LANG_PLI
dw_lang 0x0010 = DW_LANG_ObjC
dw_lang 0x0011 = DW_LANG_ObjC_plus_plus
dw_lang 0x0012 = DW_LANG_UPC
dw_lang 0x0013 = DW_LANG_D
dw_lang n = error $ "Unrecognized DW_LANG " ++ show n

data DW_ID
    = DW_ID_case_sensitive
    | DW_ID_up_case
    | DW_ID_down_case
    | DW_ID_case_insensitive
    deriving (Show, Eq)
dw_id 0x00 = DW_ID_case_sensitive
dw_id 0x01 = DW_ID_up_case
dw_id 0x02 = DW_ID_down_case
dw_id 0x03 = DW_ID_case_insensitive

data DW_CC
    = DW_CC_normal
    | DW_CC_program
    | DW_CC_nocall
    deriving (Show, Eq)
dw_cc 0x01 = DW_CC_normal
dw_cc 0x02 = DW_CC_program
dw_cc 0x03 = DW_CC_nocall
dw_cc n = error $ "Unrecognized calling convention " ++ show n

data DW_INL
    = DW_INL_not_inlined
    | DW_INL_inlined
    | DW_INL_declared_not_inlined
    | DW_INL_declared_inlined
    deriving (Show, Eq)
dw_inl 0x00 = DW_INL_not_inlined
dw_inl 0x01 = DW_INL_inlined
dw_inl 0x02 = DW_INL_declared_not_inlined
dw_inl 0x03 = DW_INL_declared_inlined

data DW_ORD
    = DW_ORD_row_major
    | DW_ORD_col_major
    deriving (Show, Eq)
dw_ord 0x00 = DW_ORD_row_major
dw_ord 0x01 = DW_ORD_col_major

data DW_DSC
    = DW_DSC_label
    | DW_DSC_range
    deriving (Show, Eq)
dw_dsc 0x00 = DW_DSC_label
dw_dsc 0x01 = DW_DSC_range

