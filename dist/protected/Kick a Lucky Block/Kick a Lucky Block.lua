-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'H5tjI9womVmcbyW8GqF1HFsU'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-IJ822BGM3vK9
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, watermark = 'Y2k-IJ822BGM3vK9', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
