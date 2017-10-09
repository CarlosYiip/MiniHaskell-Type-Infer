{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_minhs (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/carlosye/Library/Haskell/bin"
libdir     = "/Users/carlosye/Library/Haskell/ghc-8.0.2-x86_64/lib/minhs-0.1.0.0"
dynlibdir  = "/Users/carlosye/Library/Haskell/ghc-8.0.2-x86_64/lib/x86_64-osx-ghc-8.0.2"
datadir    = "/Users/carlosye/Library/Haskell/share/ghc-8.0.2-x86_64/minhs-0.1.0.0"
libexecdir = "/Users/carlosye/Library/Haskell/libexec"
sysconfdir = "/Users/carlosye/Library/Haskell/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "minhs_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "minhs_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "minhs_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "minhs_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "minhs_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "minhs_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
